"""Build the kernel proofs for independent floor bands with bounded concurrency.

The last page of each floor imports every preceding page for that floor.
A successful subprocess builds actual declarations; the final aggregation
remains an ordinary Lake target with its own axiom audit.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
import os
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parent


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--jobs", type=int, default=2)
    p.add_argument("--logs", type=Path, required=True)
    p.add_argument("--slab", choices=["narrow","lower","upper"], action="append")
    args = p.parse_args()
    if args.jobs <= 0:
        p.error("--jobs must be positive")
    args.logs = args.logs.resolve()
    args.logs.mkdir(exist_ok=True, parents=True)
    source = (ROOT/"BandRowsDecided.lean").read_text("utf8")
    modules = re.findall(r"^import (BandRows(?:Narrow|Lower|Upper)[0-9]+)$", source, re.M)
    if len(modules) != 14 + 49 + 49 or len(set(modules)) != len(modules):
        raise SystemExit("Generate one dependency chain per floor first.")
    if args.slab:
        modules = [m for m in modules if any(s.title() in m for s in args.slab)]
    env = dict(os.environ)
    env.setdefault("LEAN_NUM_THREADS","1")

    def build(name):
        start = time.monotonic()
        path = args.logs/(name+".log")
        with path.open("wb") as log:
            result = subprocess.run(["lake","--no-cache","build","+"+name], cwd=ROOT, env=env,
                                    stdout=log, stderr=subprocess.STDOUT)
        if result.returncode:
            raise RuntimeError(f"{name} exited {result.returncode}. See {path}")
        return f"{name}: {time.monotonic()-start:.1f}s"

    print(build("BandLocalProof"), flush=True)
    print(build("BandNodeData"), flush=True)
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        jobs = [pool.submit(build, name) for name in modules]
        try:
            for job in as_completed(jobs):
                print(job.result(),flush=True)
        except BaseException:
            for job in jobs:
                job.cancel()
            raise
    if not args.slab:
        print(build("BandRowsDecided"), flush=True)


if __name__ == "__main__":
    main()
