# -*- coding: utf-8 -*-
"""
Batch 28.11 — ayah-level completion targeting (diagnostics + ranking).

Does not change comparator acceptance. Uses per-ayah truth/structured rows from a comparison run.
"""

from __future__ import annotations

import csv
import json
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Tuple

from orchestrator.quran_gold.ayah_unlock_ranker import (
    AYAH_UNLOCK_NEAR_PASS_1,
    AYAH_UNLOCK_NEAR_PASS_2,
    AYAH_UNLOCK_PASS_STRICT,
    _primary_blocker_kind,
    _row_strict_satisfied,
)

# --- CSV schemas (Batch 28.11) ---

AYAH_COMPLETION_RANKING_FIELDS = (
    "surah",
    "ayah",
    "current_status",
    "strict_rows_in_ayah",
    "trapped_strict_rows",
    "blocker_token_count",
    "likely_unlock_if_one_fixed",
    "likely_unlock_if_two_fixed",
    "dominant_blocker_type",
    "recommended_priority",
    "notes",
)

TARGET_AYAHS_FIELDS = (
    "surah",
    "ayah",
    "why_selected",
    "blocker_tokens",
    "blocker_family",
    "safe_to_attempt",
    "expected_result_if_fixed",
    "notes",
)

PROMOTED_AYAHS_FIELDS = (
    "surah",
    "ayah",
    "previous_status",
    "new_status",
    "blocker_family_fixed",
    "rows_promoted",
    "became_pass_strict",
    "notes",
)

STILL_BLOCKED_AYAHS_FIELDS = (
    "surah",
    "ayah",
    "blocker_tokens",
    "blocker_type",
    "reason",
    "true_conflict",
    "review_needed",
    "notes",
)

BLOCKER_TOKEN_EXAMPLES_FIELDS = (
    "surah",
    "ayah",
    "word",
    "old_role",
    "new_role",
    "old_status",
    "new_status",
    "blocker_family",
    "promoted",
    "notes",
)


def _tier_strict(eligible: str, tier: str) -> bool:
    return "strict" in (eligible or "").lower() or tier in ("strict_structural_match", "exact_text_match")


def _truth_blockers(truth_rows: Sequence[Dict[str, Any]]) -> List[Dict[str, Any]]:
    return [r for r in truth_rows if not _row_strict_satisfied(r)]


def _strict_row_count(truth_rows: Sequence[Dict[str, Any]], structured_rows: Sequence[Dict[str, Any]]) -> int:
    _ = structured_rows
    return sum(1 for r in truth_rows if _row_strict_satisfied(r))


def _trapped_strict_count(structured_rows: Sequence[Dict[str, Any]], ayah_decision: str) -> int:
    if ayah_decision == "PASS_STRICT":
        return 0
    return sum(
        1
        for s in structured_rows
        if _tier_strict(s.get("strict_acceptance_eligible", ""), s.get("comparator_tier", ""))
    )


def _dominant_blocker_type(blockers: Sequence[Dict[str, Any]]) -> str:
    if not blockers:
        return ""
    kinds = [_primary_blocker_kind(b) for b in blockers]
    from collections import Counter

    return Counter(kinds).most_common(1)[0][0]


def build_ayah_completion_ranking_row(
    surah: int,
    ayah: int,
    runner_decision: str,
    truth_rows: Sequence[Dict[str, Any]],
    structured_rows: Sequence[Dict[str, Any]],
    unlock_label: str,
) -> Dict[str, Any]:
    """One row for ayah_completion_ranking.csv."""
    blockers = _truth_blockers(truth_rows)
    bn = len(blockers)
    strict_in = _strict_row_count(truth_rows, structured_rows)
    trapped = _trapped_strict_count(structured_rows, runner_decision)
    dom = _dominant_blocker_type(blockers)

    likely1 = unlock_label == AYAH_UNLOCK_NEAR_PASS_1 and bn == 1
    likely2 = unlock_label in (AYAH_UNLOCK_NEAR_PASS_1, AYAH_UNLOCK_NEAR_PASS_2) and bn <= 2

    pri = 99
    notes_parts: List[str] = []
    if unlock_label == AYAH_UNLOCK_NEAR_PASS_1 and bn == 1:
        pri = 1
        notes_parts.append("single_blocker")
    elif unlock_label == AYAH_UNLOCK_NEAR_PASS_2 and bn == 2:
        pri = 2
        notes_parts.append("two_blockers")
    elif trapped >= 3 and bn <= 4:
        pri = 5
        notes_parts.append("high_trapped_strict")
    if dom == "requires_core":
        notes_parts.append("core_heavy")
    if dom == "true_conflict":
        notes_parts.append("conflict_heavy")
        pri = min(pri + 10, 99)

    return {
        "surah": surah,
        "ayah": ayah,
        "current_status": unlock_label,
        "strict_rows_in_ayah": strict_in,
        "trapped_strict_rows": trapped,
        "blocker_token_count": bn,
        "likely_unlock_if_one_fixed": str(likely1).lower(),
        "likely_unlock_if_two_fixed": str(likely2).lower(),
        "dominant_blocker_type": dom,
        "recommended_priority": str(pri),
        "notes": ";".join(notes_parts) if notes_parts else f"{unlock_label}|{runner_decision}",
    }


def classify_unlock_label_from_decision_and_truth(
    decision: str,
    truth_rows: Sequence[Dict[str, Any]],
) -> str:
    """Map runner decision + truth rows to Batch 28.9-style unlock label."""
    from orchestrator.quran_gold.ayah_batch_runner import AyahDecision
    from orchestrator.quran_gold.ayah_unlock_ranker import classify_ayah_unlock_status

    dmap = {
        "PASS_STRICT": AyahDecision.PASS_STRICT,
        "FAIL_ALIGNMENT": AyahDecision.FAIL_ALIGNMENT,
        "FAIL_COMPARATOR": AyahDecision.FAIL_COMPARATOR,
        "FAIL_ANALYSIS": AyahDecision.FAIL_ANALYSIS,
        "REVIEW_NEEDED": AyahDecision.REVIEW_NEEDED,
    }
    dec = dmap.get(decision, AyahDecision.FAIL_COMPARATOR)
    label, _ = classify_ayah_unlock_status(dec, truth_rows)
    return label


def build_ranking_rows_from_snapshots(snapshots: Sequence[Dict[str, Any]]) -> List[Dict[str, Any]]:
    out: List[Dict[str, Any]] = []
    for sn in snapshots:
        surah, ayah = int(sn["surah"]), int(sn["ayah"])
        dec = (sn.get("decision") or "").strip()
        truth = sn.get("truth_audit_rows") or []
        struct = sn.get("structured_debug_rows") or []
        label = classify_unlock_label_from_decision_and_truth(dec, truth)
        out.append(
            build_ayah_completion_ranking_row(surah, ayah, dec, truth, struct, label)
        )
    return out


def select_target_ayahs(
    ranking_rows: Sequence[Dict[str, Any]],
    *,
    max_targets: int = 5,
) -> List[Dict[str, Any]]:
    """Pick top completion candidates (low priority number first)."""
    scored: List[Tuple[int, Dict[str, Any]]] = []
    for r in ranking_rows:
        try:
            pri = int(str(r.get("recommended_priority") or "99"))
        except ValueError:
            pri = 99
        st = (r.get("current_status") or "").strip()
        if st == AYAH_UNLOCK_PASS_STRICT:
            continue
        if st in ("TRUE_CONFLICT", "ALIGNMENT_BLOCKED"):
            continue
        scored.append((pri, r))
    scored.sort(key=lambda x: (x[0], -int(x[1].get("trapped_strict_rows") or 0)))
    out: List[Dict[str, Any]] = []
    for pri, r in scored[:max_targets]:
        btokens = ""
        bfam = r.get("dominant_blocker_type") or ""
        safe = (r.get("likely_unlock_if_one_fixed") == "true") or (
            pri <= 2 and (r.get("blocker_token_count") or 99) <= 2
        )
        out.append(
            {
                "surah": r.get("surah"),
                "ayah": r.get("ayah"),
                "why_selected": f"priority={pri};status={r.get('current_status')};blockers={r.get('blocker_token_count')}",
                "blocker_tokens": btokens,
                "blocker_family": bfam,
                "safe_to_attempt": str(safe).lower(),
                "expected_result_if_fixed": "PASS_STRICT" if safe else "maybe_partial",
                "notes": r.get("notes") or "",
            }
        )
    return out


def enrich_target_rows_with_blocker_words(
    targets: List[Dict[str, Any]],
    truth_by_ayah: Dict[Tuple[int, int], List[Dict[str, Any]]],
) -> None:
    for t in targets:
        sk = (int(t["surah"]), int(t["ayah"]))
        rows = truth_by_ayah.get(sk) or []
        words = [(r.get("word") or "").strip() for r in rows if not _row_strict_satisfied(r)]
        t["blocker_tokens"] = "|".join(words[:8])


def build_promoted_ayah_rows(
    per_ayah_before_status: Dict[str, str],
    snapshots: Sequence[Dict[str, Any]],
) -> List[Dict[str, Any]]:
    """Ayahs that moved to PASS_STRICT vs baseline status string."""
    promoted: List[Dict[str, Any]] = []
    for sn in snapshots:
        dec = (sn.get("decision") or "").strip()
        if dec != "PASS_STRICT":
            continue
        s, a = int(sn["surah"]), int(sn["ayah"])
        key = f"{s}:{a}"
        prev = per_ayah_before_status.get(key, "")
        if prev == "PASS_STRICT":
            continue
        truth_rows = sn.get("truth_audit_rows") or []
        nrows = len([x for x in truth_rows if _row_strict_satisfied(x)])
        promoted.append(
            {
                "surah": s,
                "ayah": a,
                "previous_status": prev or "unknown",
                "new_status": "PASS_STRICT",
                "blocker_family_fixed": "B28_11_mudaf_ilayh_or_prior_batches",
                "rows_promoted": str(nrows),
                "became_pass_strict": "true",
                "notes": "Ayah-level PASS_STRICT after Batch 28.11 L17 + ranking run",
            }
        )
    return promoted


def build_still_blocked_target_rows(
    targets: Sequence[Dict[str, Any]],
    snapshots_by_key: Dict[Tuple[int, int], Dict[str, Any]],
) -> List[Dict[str, Any]]:
    out: List[Dict[str, Any]] = []
    for t in targets:
        sk = (int(t["surah"]), int(t["ayah"]))
        sn = snapshots_by_key.get(sk) or {}
        dec = (sn.get("decision") or "").strip()
        if dec == "PASS_STRICT":
            continue
        truth_rows = sn.get("truth_audit_rows") or []
        blockers = _truth_blockers(truth_rows)
        words = "|".join((b.get("word") or "").strip() for b in blockers[:6])
        dom = _dominant_blocker_type(blockers)
        reason = "|".join((b.get("audit_bucket") or "") for b in blockers[:3])
        tc = "true" if dom == "true_conflict" else "false"
        rn = "true" if "REVIEW" in (dec or "") or dom == "other" else "false"
        out.append(
            {
                "surah": t["surah"],
                "ayah": t["ayah"],
                "blocker_tokens": words,
                "blocker_type": dom,
                "reason": reason[:300],
                "true_conflict": tc,
                "review_needed": rn,
                "notes": f"decision={dec}",
            }
        )
    return out


def build_blocker_token_examples(
    targets: Sequence[Dict[str, Any]],
    snapshots_by_key: Dict[Tuple[int, int], Dict[str, Any]],
) -> List[Dict[str, Any]]:
    """Token-level rows for selected targets (best-effort from truth audit)."""
    rows: List[Dict[str, Any]] = []
    for t in targets:
        sk = (int(t["surah"]), int(t["ayah"]))
        sn = snapshots_by_key.get(sk) or {}
        truth_rows = sn.get("truth_audit_rows") or []
        for tr in truth_rows:
            if _row_strict_satisfied(tr):
                tier = (tr.get("comparator_tier_current") or "").strip()
                if tier in ("strict_structural_match", "exact_text_match"):
                    rows.append(
                        {
                            "surah": tr.get("surah"),
                            "ayah": tr.get("ayah"),
                            "word": (tr.get("word") or "").strip(),
                            "old_role": "",
                            "new_role": (tr.get("l17_i3rab_blob_or_summary") or "")[:80],
                            "old_status": "",
                            "new_status": "accepted",
                            "blocker_family": "resolved_row",
                            "promoted": "true",
                            "notes": f"tier={tier}",
                        }
                    )
                continue
            rows.append(
                {
                    "surah": tr.get("surah"),
                    "ayah": tr.get("ayah"),
                    "word": (tr.get("word") or "").strip(),
                    "old_role": (tr.get("l17_i3rab_blob_or_summary") or "")[:80],
                    "new_role": "",
                    "old_status": (tr.get("audit_bucket") or "")[:80],
                    "new_status": "",
                    "blocker_family": _primary_blocker_kind(tr),
                    "promoted": "false",
                    "notes": (tr.get("acceptance_blocker") or "")[:120],
                }
            )
    return rows[:200]


def write_csv(path: Path, fieldnames: Sequence[str], rows: Sequence[Dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w", newline="", encoding="utf-8-sig") as f:
        w = csv.DictWriter(f, fieldnames=list(fieldnames))
        w.writeheader()
        for r in rows:
            w.writerow({k: r.get(k, "") for k in fieldnames})


def write_json(path: Path, data: Dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")
