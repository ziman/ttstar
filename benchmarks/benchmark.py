#!/usr/bin/env python3

import sys
import csv
import time
import logging
import subprocess
import collections

logging.basicConfig(level=logging.DEBUG)
log = logging.getLogger(__name__)

Input = collections.namedtuple('Input', 'lo hi step')
Program = collections.namedtuple('Program', 'inputs is_epolymorphic')
ProgramInputs = collections.namedtuple('ProgramInputs', 'erased_interpreted unerased_interpreted erased_compiled unerased_compiled')

WARMUPS = 1
SAMPLES = 2

PROGRAMS = {
    'palindrome': Program(
        inputs = ProgramInputs(
            unerased_interpreted = Input(lo=1, hi=64, step=1),
            unerased_compiled = Input(lo=1, hi=256, step=4*1),
            erased_interpreted = Input(lo=1, hi=64*1024, step=1024),
            erased_compiled = Input(lo=1, hi=1024*1024, step=4*1024),
        ),
        is_epolymorphic = False,
    ),
}

PROGRAMS = {
    'bin': Program(
        inputs = ProgramInputs(
            unerased_interpreted = Input(lo=1, hi=18, step=1),
            unerased_compiled = Input(lo=1, hi=21, step=1),
            erased_interpreted = Input(lo=1, hi=64*1024, step=2*1024),
            erased_compiled = Input(lo=1, hi=1024*1024, step=32*1024),
        ),
        is_epolymorphic = False,
    ),
}

CSV_FIELDS = (
    'program',
    'inference',
    'specialisation',
    'verification',
    'normalisation',
    'compilation',
    'input_size',
    'sample_no',
    'stage',  # ttstar, csc, execution
    'runtime',
)

def time_cmd(cmd):
    ts_start = time.perf_counter()
    subprocess.check_call(cmd, stdout=subprocess.DEVNULL)
    ts_end = time.perf_counter()

    return ts_end - ts_start

def bench_cmd(cmd):
    try:

        for _ in range(WARMUPS):
            time_cmd(cmd)

        for i in range(SAMPLES):
            yield (i, time_cmd(cmd))

    except subprocess.CalledProcessError:
        yield (0, None)

def bench_program(prog_name, prog):
    for inference in (True, False):
        if prog.is_epolymorphic:
            specs = (True, False)
        else:
            specs = (False,)

        for specialisation in specs:
            for verification in (True, False):
                for normalisation in (True, False):
                    ttstar_cmd = ["../ttstar", "../examples/%s.tt" % prog_name]
                    if not inference:
                        ttstar_cmd += ["--skip-inference"]
                    if not specialisation:
                        ttstar_cmd += ["--skip-specialisation"]
                    if not verification:
                        ttstar_cmd += ["--skip-verification"]

                    if normalisation:
                        ttstar_cmd += ["--dump-nf-scheme", "x.scm"]
                    else:
                        ttstar_cmd += ["--dump-scheme", "x.scm"]

                    config = {
                        'program': prog_name,
                        'inference': inference,
                        'specialisation': specialisation,
                        'verification': verification,
                        'normalisation': normalisation,
                        'compilation': None,
                        'input_size': None,
                    }

                    for sample_no, runtime in bench_cmd(ttstar_cmd):
                        yield {
                            'sample_no': sample_no,
                            'stage': 'ttstar',
                            'runtime': runtime,
                            **config
                        }

                    for compilation in (True, False):
                        config['compilation'] = compilation

                        if compilation:
                            for sample_no, runtime in bench_cmd(['csc', 'x.scm']):
                                yield {
                                    'sample_no': sample_no,
                                    'stage': 'csc',
                                    'runtime': runtime,
                                    **config
                                }

                            exec_cmd = ["./x"]
                            if inference:
                                inp = prog.inputs.erased_compiled
                            else:
                                inp = prog.inputs.unerased_compiled
                        else:
                            exec_cmd = ["csi", "-qs", "x.scm"]
                            if inference:
                                inp = prog.inputs.erased_interpreted
                            else:
                                inp = prog.inputs.unerased_interpreted
            
                        for input_size in range(inp.lo, inp.hi, inp.step):
                            config['input_size'] = input_size

                            for sample_no, runtime in bench_cmd(exec_cmd + [str(input_size)]):
                                yield {
                                    'sample_no': sample_no,
                                    'runtime': runtime,
                                    'stage': 'execution',
                                    **config
                                }

def main():
    subprocess.check_call('(cd ..; cabal install -j1)', shell=True)

    with open('benchmark.csv', 'w') as f:
        cw = csv.DictWriter(f, fieldnames=CSV_FIELDS)
        cw.writeheader()

        for prog_name, prog in PROGRAMS.items():
            for result in bench_program(prog_name, prog):
                cw.writerow(result)
                log.debug(result)

if __name__ == '__main__':
    main()
