package main

import (
	"bytes"
	"errors"
	"flag"
	"fmt"
	"os"
	"path/filepath"
	"sort"
	"strconv"
	"sync"
	"time"

	"github.com/google/syzkaller/pkg/csource"
	"github.com/google/syzkaller/pkg/host"
	"github.com/google/syzkaller/pkg/instance"
	"github.com/google/syzkaller/pkg/log"
	"github.com/google/syzkaller/pkg/mgrconfig"
	"github.com/google/syzkaller/pkg/osutil"
	"github.com/google/syzkaller/pkg/report"
	"github.com/google/syzkaller/pkg/report/crash"
	"github.com/google/syzkaller/prog"
	"github.com/google/syzkaller/sys/targets"
	"github.com/google/syzkaller/vm"
)

type Result struct {
	Prog     *prog.Prog
	Duration time.Duration
	Opts     csource.Options
	CRepro   bool
	// Information about the final (non-symbolized) crash that we reproduced.
	// Can be different from what we started reproducing.
	Report *report.Report
}

type Stats struct {
	Log              []byte
	ExtractProgTime  time.Duration
	MinimizeProgTime time.Duration
	SimplifyProgTime time.Duration
	ExtractCTime     time.Duration
	SimplifyCTime    time.Duration
}

type reproInstance struct {
	index    int
	execProg execInterface
}

type context struct {
	logf         func(string, ...interface{})
	target       *targets.Target
	reporter     *report.Reporter
	crashTitle   string
	crashType    crash.Type
	crashStart   int
	entries      []*prog.LogEntry
	instances    chan *reproInstance
	bootRequests chan int
	testTimeouts []time.Duration
	startOpts    csource.Options
	stats        *Stats
	report       *report.Report
	timeouts     targets.Timeouts
}

// execInterface describes what's needed from a VM by a pkg/repro.
type execInterface interface {
	Close()
	RunCProg(p *prog.Prog, duration time.Duration, opts csource.Options) (*instance.RunResult, error)
	RunSyzProg(syzProg []byte, duration time.Duration, opts csource.Options) (*instance.RunResult, error)
}

var ErrNoPrograms = errors.New("crash log does not contain any programs")

func Run(crashLog []byte, cfg *mgrconfig.Config, features *host.Features, reporter *report.Reporter,
	vmPool *vm.Pool, vmIndexes []int) (*Result, *Stats, error) {
	ctx, err := prepareCtx(crashLog, cfg, features, reporter, len(vmIndexes))
	if err != nil {
		return nil, nil, err
	}
	var wg sync.WaitGroup
	wg.Add(1)
	go func() {
		defer wg.Done()
		ctx.createInstances(cfg, vmPool)
	}()
	// Prepare VMs in advance.
	for _, idx := range vmIndexes {
		ctx.bootRequests <- idx
	}
	// Wait until all VMs are really released.
	defer wg.Wait()
	defer close(ctx.bootRequests)
	ctx.analyse()
	return nil, nil, err
}

func prepareCtx(crashLog []byte, cfg *mgrconfig.Config, features *host.Features, reporter *report.Reporter,
	VMs int) (*context, error) {
	if VMs == 0 {
		return nil, fmt.Errorf("no VMs provided")
	}
	entries := cfg.Target.ParseLog(crashLog)
	if len(entries) == 0 {
		return nil, ErrNoPrograms
	}
	crashStart := len(crashLog)
	crashTitle, crashType := "", crash.UnknownType
	if rep := reporter.Parse(crashLog); rep != nil {
		crashStart = rep.StartPos
		crashTitle = rep.Title
		crashType = rep.Type
	}
	testTimeouts := []time.Duration{
		3 * cfg.Timeouts.Program, // to catch simpler crashes (i.e. no races and no hangs)
		20 * cfg.Timeouts.Program,
		cfg.Timeouts.NoOutputRunningTime, // to catch "no output", races and hangs
	}
	switch {
	case crashTitle == "":
		crashTitle = "no output/lost connection"
		// Lost connection can be detected faster,
		// but theoretically if it's caused by a race it may need the largest timeout.
		// No output can only be reproduced with the max timeout.
		// As a compromise we use the smallest and the largest timeouts.
		testTimeouts = []time.Duration{testTimeouts[0], testTimeouts[2]}
	case crashType == crash.MemoryLeak:
		// Memory leaks can't be detected quickly because of expensive setup and scanning.
		testTimeouts = testTimeouts[1:]
	case crashType == crash.Hang:
		testTimeouts = testTimeouts[2:]
	}
	ctx := &context{
		target:       cfg.SysTarget,
		reporter:     reporter,
		crashTitle:   crashTitle,
		crashType:    crashType,
		crashStart:   crashStart,
		entries:      entries,
		instances:    make(chan *reproInstance, VMs),
		bootRequests: make(chan int, VMs),
		testTimeouts: testTimeouts,
		startOpts:    createStartOptions(cfg, features, crashType),
		stats:        new(Stats),
		timeouts:     cfg.Timeouts,
	}
	ctx.analyseLogf(0, "%v programs, %v VMs, timeouts %v", len(entries), VMs, testTimeouts)
	return ctx, nil
}

func createStartOptions(cfg *mgrconfig.Config, features *host.Features,
	crashType crash.Type) csource.Options {
	opts := csource.DefaultOpts(cfg)
	if crashType == crash.MemoryLeak {
		opts.Leak = true
	}
	if features != nil {
		if !features[host.FeatureNetInjection].Enabled {
			opts.NetInjection = false
		}
		if !features[host.FeatureNetDevices].Enabled {
			opts.NetDevices = false
		}
		if !features[host.FeatureDevlinkPCI].Enabled {
			opts.DevlinkPCI = false
		}
		if !features[host.FeatureNicVF].Enabled {
			opts.NicVF = false
		}
		if !features[host.FeatureUSBEmulation].Enabled {
			opts.USB = false
		}
		if !features[host.FeatureVhciInjection].Enabled {
			opts.VhciInjection = false
		}
		if !features[host.FeatureWifiEmulation].Enabled {
			opts.Wifi = false
		}
		if !features[host.Feature802154Emulation].Enabled {
			opts.IEEE802154 = false
		}
		if !features[host.FeatureSwap].Enabled {
			opts.Swap = false
		}
	}
	return opts
}

func (ctx *context) analyse() {
	// Cut programs that were executed after crash.
	// FIXME: May cause errors
	start := time.Now()
	defer func() {
		ctx.stats.ExtractProgTime = time.Since(start)
	}()

	for i, ent := range ctx.entries {
		if ent.Start > ctx.crashStart {
			ctx.entries = ctx.entries[:i]
			break
		}
	}

	// Extract last program on every proc.
	procs := make(map[int]int)
	for i, ent := range ctx.entries {
		procs[ent.Proc] = i
	}
	var indices []int
	for _, idx := range procs {
		indices = append(indices, idx)
	}
	sort.Ints(indices)

	var lastEntries []*prog.LogEntry
	for i := len(indices) - 1; i >= 0; i-- {
		lastEntries = append(lastEntries, ctx.entries[indices[i]])
	}

	ctx.saveLastEntries(lastEntries)
	ctx.saveEntries()

	reproStart := time.Now()
	defer func() {
		ctx.analyseLogf(3, "reproducing took %s", time.Since(reproStart))
	}()

	for _, timeout := range ctx.testTimeouts {
		ctx.extractProgAll(ctx.entries, timeout)
	}
}

func (ctx *context) extractProgAll(entries []*prog.LogEntry, baseDuration time.Duration) (*Result, error) {
	ctx.analyseLogf(3, "all: executing %d programs with timeout %s", len(entries), baseDuration)
	opts := ctx.startOpts
	duration := func(entries int) time.Duration {
		return baseDuration + time.Duration(entries/4)*time.Second
	}

	crashed, err := ctx.testProgs(entries, duration(len(entries)), opts)
	res := &Result{}
	if crashed {
		dur := duration(len(entries)) * 3 / 2
		res = &Result{
			Prog:     nil, // not only one prog
			Duration: dur,
			Opts:     opts,
		}
		ctx.analyseLogf(3, "executing %d all entries really cause crash.", len(entries))
	}
	return res, err
}

func checkOpts(opts *csource.Options, timeouts targets.Timeouts, timeout time.Duration) bool {
	if !opts.Repeat && timeout >= time.Minute {
		// If we have a non-repeating C reproducer with timeout > vm.NoOutputTimeout and it hangs
		// (the reproducer itself does not terminate on its own, note: it does not have builtin timeout),
		// then we will falsely detect "not output from test machine" kernel bug.
		// We could fix it by adding a builtin timeout to such reproducers (like we have in all other cases).
		// However, then it will exit within few seconds and we will finish the test without actually waiting
		// for full vm.NoOutputTimeout, which breaks the whole reason of using vm.NoOutputTimeout in the first
		// place. So we would need something more elaborate: let the program exist after few seconds, but
		// continue waiting for kernel hang errors for minutes, but at the same time somehow ignore "no output"
		// error because it will be false in this case.
		// Instead we simply prohibit !Repeat with long timeouts.
		// It makes sense on its own to some degree: if we are chasing an elusive bug, repeating the test
		// will increase chances of reproducing it and can make the reproducer less flaky.
		// Syz repros does not have this problem because they always have internal timeout, however
		// (1) it makes sense on its own, (2) we will either not use the whole timeout or waste the remaining
		// time as mentioned above, (3) if we remove repeat for syz repro, we won't be able to handle it
		// when/if we switch to C repro (we can simplify options, but we can't "complicate" them back).
		return false
	}
	return true
}

func (ctx *context) testProg(p *prog.Prog, duration time.Duration, opts csource.Options) (crashed bool, err error) {
	entry := prog.LogEntry{P: p}
	return ctx.testProgs([]*prog.LogEntry{&entry}, duration, opts)
}

func (ctx *context) testWithInstance(callback func(execInterface) (rep *instance.RunResult,
	err error)) (bool, error) {
	var result *instance.RunResult
	var err error

	const attempts = 3
	for i := 0; i < attempts; i++ {
		// It's hard to classify all kinds of errors into the one worth repeating
		// and not. So let's just retry runs for all errors.
		// If the problem is transient, it will likely go away.
		// If the problem is permanent, it will just be the same.
		result, err = ctx.runOnInstance(callback)
		if err == nil {
			break
		}
	}
	if err != nil {
		return false, err
	}
	rep := result.Report
	if rep == nil {
		return false, nil
	}
	// add ctx.crashTitle compare to rep.Title and rep.AltTitles
	// we may want to reproduce bugA but crash with bugB
	if ctx.crashTitle != rep.Title {
		var bias = true
		for i := range rep.AltTitles {
			if ctx.crashTitle == rep.AltTitles[i] {
				bias = false
				break
			}
		}
		if bias {
			ctx.saveAltTitle(ctx.crashTitle)
			// return false, nil
		}
	}

	if rep.Suppressed {
		ctx.analyseLogf(2, "suppressed program crash: %v", rep.Title)
		return false, nil
	}
	if ctx.crashType == crash.MemoryLeak && rep.Type != crash.MemoryLeak {
		ctx.analyseLogf(2, "not a leak crash: %v", rep.Title)
		return false, nil
	}
	ctx.report = rep
	return true, nil
}

var ErrNoVMs = errors.New("all VMs failed to boot")

// A helper method for testWithInstance.
func (ctx *context) runOnInstance(callback func(execInterface) (rep *instance.RunResult,
	err error)) (*instance.RunResult, error) {
	inst := <-ctx.instances
	if inst == nil {
		return nil, ErrNoVMs
	}
	defer ctx.returnInstance(inst)
	return callback(inst.execProg)
}

func encodeEntries(entries []*prog.LogEntry) []byte {
	buf := new(bytes.Buffer)
	for _, ent := range entries {
		fmt.Fprintf(buf, "executing program %v:\n%v", ent.Proc, string(ent.P.Serialize()))
	}
	return buf.Bytes()
}

func (ctx *context) testProgs(entries []*prog.LogEntry, duration time.Duration, opts csource.Options) (
	crashed bool, err error) {
	if len(entries) == 0 {
		return false, fmt.Errorf("no programs to execute")
	}
	pstr := encodeEntries(entries)
	program := entries[0].P.String()
	if len(entries) > 1 {
		program = "["
		for i, entry := range entries {
			program += fmt.Sprintf("%v", len(entry.P.Calls))
			if i != len(entries)-1 {
				program += ", "
			}
		}
		program += "]"
	}
	ctx.analyseLogf(2, "testing program (duration=%v, %+v): %s", duration, opts, program)
	ctx.analyseLogf(4, "detailed listing:\n%s", pstr)
	return ctx.testWithInstance(func(exec execInterface) (*instance.RunResult, error) {
		return exec.RunSyzProg(pstr, duration, opts)
	})
}

func (ctx *context) returnInstance(inst *reproInstance) {
	ctx.bootRequests <- inst.index
	inst.execProg.Close()
}

func (ctx *context) analyseLogf(level int, format string, args ...interface{}) {
	if ctx.logf != nil {
		ctx.logf(format, args...)
	}
	prefix := fmt.Sprintf("analysing crash '%v': ", ctx.crashTitle)
	log.Logf(level, prefix+format, args...)
	ctx.stats.Log = append(ctx.stats.Log, []byte(fmt.Sprintf(format, args...)+"\n")...)
}

func (ctx *context) createInstances(cfg *mgrconfig.Config, vmPool *vm.Pool) {
	var wg sync.WaitGroup
	for vmIndex := range ctx.bootRequests {
		wg.Add(1)
		vmIndex := vmIndex
		go func() {
			defer wg.Done()

			var inst *instance.ExecProgInstance
			maxTry := 3
			for try := 0; try < maxTry; try++ {
				select {
				case <-vm.Shutdown:
					try = maxTry
					continue
				default:
				}
				var err error
				inst, err = instance.CreateExecProgInstance(vmPool, vmIndex, cfg,
					ctx.reporter, &instance.OptionalConfig{Logf: ctx.analyseLogf})
				if err != nil {
					ctx.analyseLogf(0, "failed to init instance: %v, attempt %d/%d",
						err, try+1, maxTry)
					time.Sleep(10 * time.Second)
					continue
				}
				break
			}
			if inst != nil {
				ctx.instances <- &reproInstance{execProg: inst, index: vmIndex}
			}
		}()
	}
	wg.Wait()
	// Clean up.
	close(ctx.instances)
	for inst := range ctx.instances {
		inst.execProg.Close()
	}
}

func (ctx *context) saveLastEntries(entries []*prog.LogEntry) {
	ctx.analyseLogf(3, "save lastEntries %v progs", len(entries))
	folder := fmt.Sprintf("last-%v", strconv.FormatInt(time.Now().Unix(), 10))
	err := os.Mkdir(folder, 0755)
	if err != nil {
		ctx.analyseLogf(1, "create interesting prog folder failed")
	} else {
		for i, ent := range entries {
			f, err := os.Create(filepath.Join(folder, fmt.Sprintf("prog%v", i)))
			data := ent.P.Serialize()
			if err == nil {
				f.Write(data)
				f.Close()
			}
		}
	}
}

func (ctx *context) saveEntries() {
	ctx.analyseLogf(3, "save entries %v progs", len(ctx.entries))
	folder := fmt.Sprintf("entry-%v", strconv.FormatInt(time.Now().Unix(), 10))
	err := os.Mkdir(folder, 0755)
	if err != nil {
		ctx.analyseLogf(1, "create interesting prog folder failed")
	} else {
		for i, ent := range ctx.entries {
			f, err := os.Create(filepath.Join(folder, fmt.Sprintf("prog%v", i)))
			data := ent.P.Serialize()
			if err == nil {
				f.Write(data)
				f.Close()
			}
		}
	}
}

func (ctx *context) saveAltTitle(title string) {
	ctx.analyseLogf(3, "save crash tile %v", title)
	folder := fmt.Sprintf("repro-%v", strconv.FormatInt(time.Now().Unix(), 10))
	err := os.Mkdir(folder, 0755)
	if err != nil {
		ctx.analyseLogf(1, "create altTitle reproduce folder failed")
	} else {
		f, err := os.Create(filepath.Join(folder, "description"))
		if err == nil {
			f.Write([]byte(title))
			f.Close()
		}
	}
}

var (
	flagConfig = flag.String("config", "", "manager configuration file (manager.cfg)")
	flagCount  = flag.Int("count", 0, "number of VMs to use (overrides config count param)")
	flagDebug  = flag.Bool("debug", false, "print debug output")
	flagTitle  = flag.String("title", "", "where to save the title of the reproduced bug")
	flagStrace = flag.String("strace", "", "output strace log (strace_bin must be set)")
)

func main() {
	os.Args = append(append([]string{}, os.Args[0], "-vv=10"), os.Args[1:]...)
	flag.Parse()
	if len(flag.Args()) != 1 || *flagConfig == "" {
		log.Fatalf("usage: syz-analyse -config=manager.cfg execution.log")
	}
	cfg, err := mgrconfig.LoadFile(*flagConfig)
	if err != nil {
		log.Fatalf("%v: %v", *flagConfig, err)
	}
	logFile := flag.Args()[0]
	data, err := os.ReadFile(logFile)
	if err != nil {
		log.Fatalf("failed to open log file %v: %v", logFile, err)
	}
	vmPool, err := vm.Create(cfg, *flagDebug)
	if err != nil {
		log.Fatalf("%v", err)
	}
	vmCount := vmPool.Count()
	if *flagCount > 0 && *flagCount < vmCount {
		vmCount = *flagCount
	}
	if vmCount > 4 {
		vmCount = 4
	}
	vmIndexes := make([]int, vmCount)
	for i := range vmIndexes {
		vmIndexes[i] = i
	}
	reporter, err := report.NewReporter(cfg)
	if err != nil {
		log.Fatalf("%v", err)
	}
	osutil.HandleInterrupts(vm.Shutdown)

	Run(data, cfg, nil, reporter, vmPool, vmIndexes)
}
