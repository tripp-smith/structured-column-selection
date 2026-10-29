"""Check frozen experiment artifacts against ``experiments/manifest.json``.

The manifest records what each file is evidence of. It does not rerun the
census. A numeric record stays numeric until the manifest is edited on purpose.
"""

from __future__ import annotations

import json
import re
from pathlib import Path

NUMERIC_STATUS_MARKERS = (
    "not a theorem",
    "numerically observed",
    "not certified",
)


def load_manifest(root: Path) -> dict:
    path = root / "experiments" / "manifest.json"
    data = json.loads(path.read_text(encoding="utf-8"))
    if data.get("schema_version") != 1:
        raise ValueError("experiments/manifest.json schema_version must be 1")
    if data.get("require_clean_revision_for_new_runs") is not True:
        raise ValueError("new canonical runs must require a clean revision")
    return data


def check_manifest(root: Path) -> list[str]:
    """Return errors. An empty list means the frozen records match the manifest."""
    manifest = load_manifest(root)
    specs = manifest["artifacts"]
    errors: list[str] = []
    listed = [spec["path"] for spec in specs]
    if len(listed) != len(set(listed)):
        errors.append("manifest lists a path more than once")
    on_disk = {
        path.relative_to(root).as_posix()
        for path in (root / "experiments").glob("*.json")
        if path.name != "manifest.json"
    }
    if set(listed) != on_disk:
        missing = sorted(set(listed) - on_disk)
        extra = sorted(on_disk - set(listed))
        errors.append(f"experiment inventory mismatch: missing={missing}, extra={extra}")
    for spec in specs:
        errors.extend(_check_artifact(root, spec))
    return errors


def _check_artifact(root: Path, spec: dict) -> list[str]:
    path = root / spec["path"]
    label = spec["path"]
    errors: list[str] = []
    if spec.get("closes_milestone_e") is not False:
        errors.append(f"{label} must record closes_milestone_e false")
    evidence = spec.get("evidence")
    if evidence not in {"numeric", "certified_native_decide"}:
        errors.append(f"{label} has unknown evidence {evidence!r}")
        return errors
    if not path.is_file():
        errors.append(f"{label} is missing")
        return errors
    data = json.loads(path.read_text(encoding="utf-8"))
    container = spec.get("container", "object")
    if container == "list":
        if not isinstance(data, list) or not data:
            errors.append(f"{label} must be a non-empty list")
        return errors
    if not isinstance(data, dict):
        errors.append(f"{label} must be an object")
        return errors
    if "seed" in spec and data.get("seed") != spec["seed"]:
        errors.append(f"{label} seed {data.get('seed')!r} != {spec['seed']!r}")
    if "revision" in spec and data.get("revision") != spec["revision"]:
        errors.append(
            f"{label} revision {data.get('revision')!r} != {spec['revision']!r}"
        )
    if "any_above_named_poly" in spec and data.get("any_above_named_poly") != spec[
        "any_above_named_poly"
    ]:
        errors.append(f"{label} any_above_named_poly does not match the manifest")
    if "any_r_gt_1" in spec and data.get("any_r_gt_1") != spec["any_r_gt_1"]:
        errors.append(f"{label} any_r_gt_1 does not match the manifest")
    if spec.get("every_track_any_above_named_poly") is False:
        tracks = data.get("tracks")
        if not isinstance(tracks, list) or not tracks:
            errors.append(f"{label} must contain tracks")
        elif any(track.get("any_above_named_poly") is not False for track in tracks):
            errors.append(f"{label} has a track above the named polynomial")
    if evidence == "numeric" and "status" in data:
        status = str(data["status"]).lower()
        if not any(marker in status for marker in NUMERIC_STATUS_MARKERS):
            errors.append(f"{label} numeric status does not say it is not a theorem")
    if evidence == "certified_native_decide":
        errors.extend(_check_computational_witness(root, spec, data))
    if data.get("closes_milestone_e") not in (None, False):
        errors.append(f"{label} claims it closes Milestone E")
    return errors


def _check_computational_witness(root: Path, spec: dict, data: dict) -> list[str]:
    label = spec["path"]
    errors: list[str] = []
    certificate = data.get("certificate")
    if not isinstance(certificate, dict) or certificate.get("ok") is not True:
        errors.append(f"{label} certificate is not ok")
    lean_path = root / spec["lean_file"]
    lean_text = lean_path.read_text(encoding="utf-8")
    theorems = (root / "StructuredColumnSelection" / "Theorems.lean").read_text(
        encoding="utf-8"
    )
    for name in spec["lean_names"]:
        if name not in lean_text:
            errors.append(f"{label} witness {name} is absent from {spec['lean_file']}")
        if re.search(rf"^theorem\s+{re.escape(name)}\b", theorems, re.MULTILINE):
            errors.append(f"{name} is exported from Theorems.lean")
    return errors
