#!/usr/bin/env python3
"""Build `SimplicialHomotopy` by calling `lean` directly, without `lake`.

On a machine where `lake` works, use `lake exe cache get && lake build` instead. This script is
the fallback for machines where `lake` does not start. It compiles the modules of the library
in import order, with the `leanOptions` of `lakefile.toml`, and then prints a report on `sorry`
and axioms (`scripts/AxiomReport.lean`).

    python3 scripts/build.py            # rebuild what is stale, then the report
    python3 scripts/build.py --all      # rebuild everything
    python3 scripts/build.py -j 6       # number of parallel compilers (default 4)
    python3 scripts/build.py --no-report

It needs a compiled Mathlib at the revision pinned in `lakefile.toml`, with its dependencies.
The folder that holds the packages (`mathlib`, `batteries`, `aesop`, ...), each with its
`.lake/build/lib/lean`, is taken from

1. the environment variable `MATHLIB_BUILD`, or
2. the first line of the file `.lake/mathlib-build` (not tracked by git), or
3. `.lake/packages` of this repository, which is where `lake exe cache get` puts them.

The `lean` binary is the one of the toolchain named in `lean-toolchain`, as installed by
`elan`; set the environment variable `LEAN` to use another one.

A module is rebuilt when its `.olean` is missing, or older than its source, or older than the
`.olean` of a module of this library that it imports. Compiled files go to
`.lake/build/lib/lean`. Exit status 0 means that every module compiled and printed nothing
(no error, no warning) and that the report found no `sorry` and no new axiom.
"""
import argparse
import concurrent.futures as cf
import fcntl
import os
import pathlib
import re
import subprocess
import sys
import time

ROOT = pathlib.Path(__file__).resolve().parent.parent
NAME = "SimplicialHomotopy"
LIB = ROOT / ".lake" / "build" / "lib" / "lean"
OPTS = ["-DautoImplicit=false", "-DrelaxedAutoImplicit=false"]
IMPORT = re.compile(r"^(?:public\s+)?import\s+(" + NAME + r"(?:\.[\w']+)*)\s*$", re.M)


def lean_binary():
    if os.environ.get("LEAN"):
        return pathlib.Path(os.environ["LEAN"])
    toolchain = (ROOT / "lean-toolchain").read_text().strip()
    folder = toolchain.replace("/", "--").replace(":", "---")
    home = pathlib.Path(os.environ.get("ELAN_HOME", pathlib.Path.home() / ".elan"))
    return home / "toolchains" / folder / "bin" / "lean"


def packages_dir():
    if os.environ.get("MATHLIB_BUILD"):
        return pathlib.Path(os.environ["MATHLIB_BUILD"]).expanduser()
    note = ROOT / ".lake" / "mathlib-build"
    if note.exists():
        return pathlib.Path(note.read_text().splitlines()[0].strip()).expanduser()
    return ROOT / ".lake" / "packages"


def lean_path():
    pk = packages_dir()
    dirs = [LIB] + [p / ".lake/build/lib/lean" for p in sorted(pk.iterdir())
                    if (p / ".lake/build/lib/lean").is_dir()]
    if not (pk / "mathlib/.lake/build/lib/lean/Mathlib.olean").exists():
        sys.exit(f"no compiled Mathlib under {pk}: set MATHLIB_BUILD (see the top of this file)")
    return ":".join(str(d) for d in dirs)


def modules():
    files = [ROOT / (NAME + ".lean")] + sorted((ROOT / NAME).rglob("*.lean"))
    return {".".join(f.relative_to(ROOT).with_suffix("").parts): f for f in files}


def run_lean(args, env, stdin=None):
    r = subprocess.run([str(lean_binary()), *OPTS, *args], cwd=ROOT, env=env, input=stdin,
                       capture_output=True, text=True)
    return r.returncode, (r.stdout + r.stderr).strip()


def compile_one(name, src, env):
    out = LIB / pathlib.Path(*name.split("."))
    out.parent.mkdir(parents=True, exist_ok=True)
    t0 = time.time()
    code, text = run_lean(["-o", str(out) + ".olean", "-i", str(out) + ".ilean", str(src)], env)
    return name, code, text, time.time() - t0


def build(args, env):
    mods = modules()
    deps = {m: [d for d in IMPORT.findall(f.read_text(encoding="utf-8")) if d in mods]
            for m, f in mods.items()}
    olean = {m: LIB / (m.replace(".", "/") + ".olean") for m in mods}
    done, rebuilt, failed, noisy = set(), set(), [], []
    todo = dict(deps)
    t0 = time.time()
    with cf.ThreadPoolExecutor(max_workers=args.j) as pool:
        running = {}
        while todo or running:
            ready = [m for m, ds in todo.items() if all(d in done for d in ds)]
            while ready:
                for m in ready:
                    ds = todo.pop(m)
                    stale = (args.all or not olean[m].exists()
                             or olean[m].stat().st_mtime < mods[m].stat().st_mtime
                             or any(d in rebuilt for d in ds)
                             or any(olean[d].stat().st_mtime > olean[m].stat().st_mtime
                                    for d in ds))
                    if stale:
                        running[pool.submit(compile_one, m, mods[m], env)] = m
                    else:
                        done.add(m)
                ready = [m for m, ds in todo.items() if all(d in done for d in ds)]
            if not running:
                break
            for fut in cf.wait(running, return_when=cf.FIRST_COMPLETED).done:
                running.pop(fut)
                name, code, text, dt = fut.result()
                if code != 0:
                    failed.append(name)
                    print(f"FAILED {name} ({dt:.0f}s)\n{text}\n")
                else:
                    done.add(name)
                    rebuilt.add(name)
                    if text:
                        noisy.append(name)
                        print(f"OUTPUT {name} ({dt:.0f}s)\n{text}\n")
                    else:
                        print(f"ok     {name} ({dt:.0f}s)")
                sys.stdout.flush()
    if todo:
        print("not reached (a module they import failed):", ", ".join(sorted(todo)))
    print(f"\n{len(mods)} modules: {len(done)} ok ({len(rebuilt)} compiled now, "
          f"{len(noisy)} with output), {len(failed)} failed, {len(todo)} not reached, "
          f"{time.time() - t0:.0f}s")
    return not (failed or noisy or todo)


def report(env):
    print("\n-- sorry and axiom report --")
    code, out = run_lean([str(ROOT / "scripts" / "AxiomReport.lean")], env)
    print(out)
    return code == 0 and "REPORT: clean" in out


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--all", action="store_true", help="rebuild every module")
    ap.add_argument("-j", type=int, default=4, help="parallel compilers (default 4)")
    ap.add_argument("--no-report", action="store_true", help="skip the sorry and axiom report")
    args = ap.parse_args()
    if not lean_binary().exists():
        sys.exit(f"no lean binary at {lean_binary()}: install the toolchain or set LEAN")
    env = {**os.environ, "LEAN_PATH": lean_path()}
    LIB.mkdir(parents=True, exist_ok=True)
    lock = open(LIB / ".build.lock", "w")
    fcntl.flock(lock, fcntl.LOCK_EX)   # one build at a time
    ok = build(args, env)
    if ok and not args.no_report:
        ok = report(env)
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
