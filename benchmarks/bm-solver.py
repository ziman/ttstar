#!/usr/bin/env python3

import os
import time
import json
import subprocess

WARMUPS = 8
SAMPLES = 64

def time_cmd(cmd):
    # TODO: use perf stat -x \;
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

def main():
    print('"program","iteration","erasure","annotations","evars","annotations_used","duration"')
    for fname in os.listdir('../examples'):
        for erasure in (True, False):
            cmd = ['ttstar', '--dump-pretty', '/dev/null', '--dump-stats', '/tmp/stats.json']
            if not erasure:
                cmd += ['--skip-inference']

            for i, t in bench_cmd(cmd + ["../examples/" + fname]):
                if t is None:  # some error
                    continue

                with open('/tmp/stats.json') as f:
                    doc = json.load(f)

                print('"%s","%d","%s","%d","%d","%d","%f"' % (
                    fname.split('.')[0], i, erasure,
                    doc['annotations'], doc['evars'], doc['annotations_used'],
                    t,
                ))

if __name__ == '__main__':
    main()
