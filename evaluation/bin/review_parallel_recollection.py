#!/usr/bin/env python3
"""Compare captured parallel outputs using a frozen membership observer.

Compilation success is not an effect criterion. Reuse requires the same input,
flags, complete final Loop, and selected parallel producer C. Other pairs use
complete bounded observations; incomplete observations remain unresolved.
"""
import argparse
from collections import Counter
import hashlib
import importlib.util
import json
from pathlib import Path

from retention_candidate import select_candidate
from retention_identity import audit_scop, supports_instance_identity


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def final_loop(path):
    text = path.read_text(errors="replace")
    marker = "== Optimized Loop =="
    return text.split(marker, 1)[1].strip() if marker in text else None


def select_producer(case):
    return select_candidate(case, parallel_only=True)


def same_pair(old_case, new_case, old_row, repository):
    before = json.loads((old_case / "result.json").read_text())
    after = json.loads((new_case / "result.json").read_text())
    if any(before.get(k) != after.get(k) for k in ("id", "source_sha256", "polopt_args", "pluto_args")):
        return False
    if any(r["returncode"] or r["timed_out"] for r in (before, after)):
        return False
    if list(new_case.glob("producer-resource-*.json")):
        return False
    a, b = final_loop(old_case / "polcert.stdout.txt"), final_loop(new_case / "polcert.stdout.txt")
    if a is None or a != b:
        return False
    old_file = old_row.get("producer_file")
    old_file = repository / old_file if old_file else None
    selected = select_producer(new_case)
    if old_file is None or selected['status'] != 'selected':
        return False
    old_selection = select_candidate(old_case, parallel_only=True, explicit=old_file,
                                     expected_sha256=old_row.get('producer_sha256'))
    if old_selection['status'] != 'selected':
        return False
    return old_selection['selected']['sha256'] == selected['selected']['sha256']


def classify(observations):
    if not observations or not all(o["pluto"]["complete"] and o["polcert"]["complete"] for o in observations):
        return "unresolved-incomplete-observation"
    if any(o["pluto"].get("first_conflict") for o in observations):
        return "producer-cross-iteration-conflict"
    if not any(o["pluto"]["nontrivial_regions"] for o in observations):
        return "unresolved-producer-nontriviality"
    if all(o["complete_access_multiset_match"] and o["complete_parallel_membership_match"] for o in observations):
        return "sampled-retained"
    return "requires-mismatch-review"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("collection", type=Path)
    parser.add_argument("--reference-root", type=Path)
    parser.add_argument("--reference-review", type=Path)
    parser.add_argument("--fresh", action="store_true", help="Remeasure every pair; never read prior reviews or traces")
    parser.add_argument("--repository", type=Path, required=True)
    parser.add_argument("--source-root", type=Path, required=True)
    parser.add_argument("--observer", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--only", nargs="+")
    args = parser.parse_args()
    if args.fresh and (args.reference_root is not None or args.reference_review is not None):
        parser.error('--fresh cannot be combined with prior reference evidence')
    if not args.fresh and (args.reference_root is None or args.reference_review is None):
        parser.error('Supply --fresh or both --reference-root and --reference-review')
    observer = load_module("retention_membership_observer", args.observer)
    replay = load_module("retention_recollection_contracts", Path(__file__).with_name("retention_applicability.py"))
    observer.review.HELPERS = observer.review.HELPERS.replace("events>2000000", "events>4000000")
    transpiler = observer.review.rt.load_transpiler(args.source_root)
    prior = {} if args.fresh else {r["id"]: r for r in json.loads(args.reference_review.read_text())["rows"]}
    args.output.mkdir(parents=True, exist_ok=True)
    inputs = {"observer": sha(args.observer), "script": sha(Path(__file__)),
              "reference_review": None if args.fresh else sha(args.reference_review),
              "fresh_measurements": args.fresh,
              "instrumenter": sha(Path(observer.review.rt.__file__)),
              "build_helpers": sha(Path(observer.review.__file__)),
              "source_applicability": sha(Path(replay.__file__)),
              "candidate_selector": sha(Path(select_candidate.__code__.co_filename))}
    rows = []
    for path in sorted((args.collection / "cases").glob("*/result.json")):
        raw = json.loads(path.read_text())
        ident, case = raw["id"], path.parent
        if args.only and ident not in args.only:
            continue
        old = {} if args.fresh else prior[ident]
        selection = select_producer(case)
        producer = Path(selection['selected']['file']) if selection['status'] == 'selected' else None
        output = case / "polcert.stdout.txt"
        body = final_loop(output)
        row = {"id": ident, "source_sha256": raw["source_sha256"],
               "returncode": raw["returncode"], "timed_out": raw["timed_out"],
               "producer_file": str(producer) if producer else None,
               "producer_sha256": sha(producer) if producer else None,
               "producer_selection": selection,
               "final_file": str(output), "final_sha256": sha(output),
               "adopted_path": (case / "polcert.stderr.txt").read_text(errors="replace"),
               "producer_status": "unknown", "retention_status": "unresolved", "observations": []}
        target = args.output / ident
        target.mkdir(exist_ok=True)
        straightline = replay.source_without_loop(raw, args.source_root, case / 'source.loop')
        if straightline:
            row.update(producer_status="absent", retention_status="not-applicable")
            row["source_applicability"] = straightline
            row["failure_stage"] = replay.failure_stage(raw, row["adopted_path"])
        elif raw["returncode"] or raw["timed_out"] or not body:
            row["retention_status"] = "compilation-failure-needs-stage-review"
        elif list(case.glob("producer-resource-*.json")):
            row["retention_status"] = "external-producer-resource-limit"
        elif selection['status'].startswith('unpaired-'):
            row['retention_status'] = selection['status']
        elif not args.fresh and same_pair(args.reference_root / "cases" / ident, case, old, args.repository):
            row.update(producer_status=old["producer_status"], retention_status=old["retention_status"])
            row["evidence_reuse"] = {"file": str(args.reference_review), "sha256": sha(args.reference_review),
                                      "id": ident, "criterion": "identical-input-flags-selected-producer-C-and-complete-final-Loop"}
        elif producer is None:
            row.update(producer_status="absent", retention_status="not-applicable")
        else:
            source = case / 'source.loop'
            if not source.exists():
                source = Path(raw['loop_input'])
            if sha(source) != raw["source_sha256"]:
                raise ValueError("Changed source: " + str(source))
            params = observer.review.rt.params_from_loop(source.read_text())
            row["parameters"] = params
            samples = [o["parameters"] for o in old.get("observations", [])]
            if not samples:
                samples = [{p: 5 for p in params}]
                for parameter in params:
                    for extent, other in [(37, 3), (67, 3)]:
                        sample = {p: extent if p == parameter else other for p in params}
                        if sample not in samples:
                            samples.append(sample)
            # Fixed large domains need symbolic/static review, not prefixes.
            if not params and raw["kernel"] in ("fusion3", "fusion4"):
                row["retention_status"] = "requires-complete-static-comparison"
            else:
                try:
                    observer.review.build(observer.review.rt.instrument(producer.read_text(errors="replace"), parameters=params), params, target / "pluto")
                    observer.review.build(observer.review.rt.instrument(transpiler.transpile_loop_text(body), parameters=params), params, target / "polcert")
                    for sample in samples:
                        a = observer.run(target / "pluto", [sample[p] for p in params])
                        b = observer.run(target / "polcert", [sample[p] for p in params])
                        complete = a["complete"] and b["complete"]
                        row["observations"].append({"parameters": sample, "pluto": a, "polcert": b,
                            "complete_access_multiset_match": complete and a["access_multiset_sha256"] == b["access_multiset_sha256"],
                            "complete_parallel_membership_match": complete and a["membership_groups"] == b["membership_groups"]})
                    row["retention_status"] = classify(row["observations"])
                    row['identity_audit'] = audit_scop(producer.parent / 'input.scop')
                    if row['retention_status'] == 'sampled-retained':
                        if supports_instance_identity(row['identity_audit'], row['observations']):
                            row['evidence_level'] = 'source-instance-membership'
                        else:
                            row['evidence_level'] = 'access-membership-only'
                            row['retention_status'] = 'requires-source-instance-review'
                    row["producer_status"] = "observed" if any(o["pluto"]["nontrivial_regions"] for o in row["observations"]) else "unknown"
                except Exception as exc:
                    row["retention_status"] = "measurement-error"
                    row["error"] = str(exc)
        (target / "evidence.json").write_text(json.dumps(row, indent=2) + "\n")
        rows.append(row)
        report = {"inputs": inputs, "method": "Complete bounded access multisets and membership within each dynamic parallel region; no arithmetic-value equivalence claim. Identical complete paired outputs may reuse explicitly cited prior evidence.",
                  "counts": dict(Counter(r["retention_status"] for r in rows)), "rows": rows}
        (args.output / "review.json").write_text(json.dumps(report, indent=2) + "\n")
        print(ident, row["retention_status"], flush=True)


if __name__ == "__main__":
    main()
