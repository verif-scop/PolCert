"""Monotonic process measurements and aggregate timing statistics."""
import hashlib
import json
import math
import os
from pathlib import Path
import signal
import statistics
import subprocess
import time


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_json(path):
    return json.loads(path.read_text())


def write_json(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = Path(str(path) + ".tmp")
    temporary.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
    temporary.replace(path)


def run(command, cwd, env, destination, timeout):
    started = time.perf_counter()
    proc = subprocess.Popen(command, cwd=cwd, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            start_new_session=True)
    timed_out = False
    try:
        stdout, stderr = proc.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        timed_out = True
        os.killpg(proc.pid, signal.SIGKILL)
        stdout, stderr = proc.communicate()
    elapsed = time.perf_counter() - started
    destination.parent.mkdir(parents=True, exist_ok=True)
    Path(str(destination) + ".stdout.txt").write_text(stdout)
    Path(str(destination) + ".stderr.txt").write_text(stderr)
    return {"command": command, "cwd": str(cwd), "wall_seconds": elapsed,
            "returncode": proc.returncode, "timed_out": timed_out,
            "stdout_sha256": hashlib.sha256(stdout.encode()).hexdigest(),
            "stdout_path": str(destination) + ".stdout.txt",
            "stderr_path": str(destination) + ".stderr.txt"}, stdout, stderr


def distribution(values):
    values = sorted(values)
    position = (len(values) - 1) * 0.95
    lo, hi = math.floor(position), math.ceil(position)
    return {"count": len(values), "sum_seconds": sum(values), "mean_seconds": statistics.mean(values),
            "median_seconds": statistics.median(values), "p95_seconds": values[lo] + (position - lo) * (values[hi] - values[lo]),
            "max_seconds": values[-1]}
