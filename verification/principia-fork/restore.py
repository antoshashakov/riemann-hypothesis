"""Restore the matching, successful upstream cache with per-archive retry and verification."""
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import tempfile

root = Path.cwd()
spec = importlib.util.spec_from_file_location("official_ci_cache", root / "scripts/ci-cache-get.py")
ci = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ci)
identity = ci.current_identity(root)
assert identity["source_tree"] == "c41b34f3b5adfd4120d58bf77d87e13a785778ec"
record = ci.find_record(root, identity)
if record is None:
    raise RuntimeError("No successful cache for the exact base inputs")
_, rows = ci.validated_blobs(record, identity)
print("Verified upstream cache manifest", record["module_manifest_sha256"], "for", len(rows), "modules", flush=True)

cache = root / ".lake/cache"
archives = cache / "artifacts"
archives.mkdir(parents=True, exist_ok=True)
service = "https://rh-cache.taucetiproject.org/artifacts/leanprover-community/riemann-hypothesis"

def valid(row):
    file = archives / row[2]
    if not file.is_file():
        return False
    with file.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest() == row[3]

for start in range(0, len(rows), 4000):
    group = rows[start:start+4000]
    pending = [row for row in group if not valid(row)]
    for attempt in range(4):
        if not pending:
            break
        # Each URL and filename is a checked hexadecimal artifact key from validated_blobs.
        with tempfile.NamedTemporaryFile(mode="w", dir=cache, encoding="utf8") as config:
            for _, _, name, _ in pending:
                config.write(f'url = "{service}/{name[:-5]}.art"\noutput = "{name}"\n')
            config.flush()
            subprocess.run(["curl","--parallel","--parallel-max","100","--fail","--silent","--show-error",
                            "--retry","3","--retry-all-errors","--retry-delay","1","--connect-timeout","15",
                            "--max-time","90","--config",config.name], cwd=archives)
        pending = [row for row in pending if not valid(row)]
    if pending:
        raise RuntimeError(f"Could not obtain and authenticate {len(pending)} archives: {pending[:4]}")
    if start % 16000 == 0 or start + len(group) == len(rows):
        print("Authenticated", start + len(group), "/", len(rows), "archives", flush=True)

jobs = ci.restore.restore_jobs(root, cache, rows)
if ci.current_identity(root) != identity:
    raise RuntimeError("The base source changed during cache restoration")
for job in jobs:
    for directory in job["base"]:
        Path(directory).mkdir(parents=True, exist_ok=True)
lean = Path(subprocess.check_output(["elan","which","lean"], text=True).strip())
print("Unpacking authenticated archives with leantar", flush=True)
subprocess.run([lean.with_name("leantar"),"--jobs","4","-f","-x","-j","-"],
               input=json.dumps(jobs), text=True, check=True)
print("Full base cache restored", flush=True)
