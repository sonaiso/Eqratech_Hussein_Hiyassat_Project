# -*- coding: utf-8 -*-
"""
Extract L17 (primary) and L11 (fallback) per-token analyzer data from a pipeline dict.

Does not invoke stages — reads `layer_outputs` only.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Dict, List, Optional, Sequence

L17_MIN_CONF_CANDIDATE = 0.75


@dataclass(frozen=True)
class TokenAnalyzerSnapshot:
    token_id: str
    surface: str
    l17: Optional[Dict[str, Any]]
    l11_i3rab_text: Optional[str]
    primary_label: str  # "L17_resolved" | "L17_candidate" | "L11_only" | "none"


def get_token_surfaces(pipeline: Dict[str, Any]) -> List[str]:
    lo = pipeline.get("layer_outputs") or {}
    l2 = (lo.get("L2_TOKENIZATION") or {}).get("transformation_result") or {}
    tokens = l2.get("tokens") or []
    out: List[str] = []
    for t in tokens:
        w = (t.get("word") if isinstance(t, dict) else None) or (
            t.get("surface") if isinstance(t, dict) else None
        )
        out.append((w or "").strip())
    return out


def _l17_reasoning_list(pipeline: Dict[str, Any]) -> List[Dict[str, Any]]:
    lo = pipeline.get("layer_outputs") or {}
    tr = (lo.get("L17_RULE_BASED_I3RAB") or {}).get("transformation_result") or {}
    return list(tr.get("token_reasoning") or [])


def _l11_token_results(pipeline: Dict[str, Any]) -> List[Dict[str, Any]]:
    lo = pipeline.get("layer_outputs") or {}
    tr = (lo.get("L11_I3RAB") or {}).get("transformation_result") or {}
    return list(tr.get("token_results") or [])


def extract_snapshots(pipeline: Dict[str, Any]) -> List[TokenAnalyzerSnapshot]:
    """One snapshot per pipeline token index (string ids '0'..)."""
    surfaces = get_token_surfaces(pipeline)
    l17_by_id = {str(e.get("token_id")): e for e in _l17_reasoning_list(pipeline)}
    l11_list = _l11_token_results(pipeline)
    out: List[TokenAnalyzerSnapshot] = []
    for i, surf in enumerate(surfaces):
        tid = str(i)
        l17 = l17_by_id.get(tid)
        l11_t = l11_list[i] if i < len(l11_list) else None
        l11_txt = (l11_t.get("i3rab_text") or "").strip() if l11_t else None
        if l11_txt == "":
            l11_txt = None

        label = "none"
        if l17:
            st = (l17.get("status") or "").strip()
            conf = float(l17.get("confidence") or 0.0)
            if st == "resolved":
                label = "L17_resolved"
            elif st == "candidate" and conf >= L17_MIN_CONF_CANDIDATE:
                label = "L17_candidate"
            elif l11_txt:
                label = "L11_only"
            else:
                label = "none"
        elif l11_txt:
            label = "L11_only"
        out.append(
            TokenAnalyzerSnapshot(
                token_id=tid,
                surface=surf,
                l17=l17,
                l11_i3rab_text=l11_txt,
                primary_label=label,
            )
        )
    return out


def snapshot_for_token_index(snapshots: Sequence[TokenAnalyzerSnapshot], idx: int) -> Optional[TokenAnalyzerSnapshot]:
    if idx < 0 or idx >= len(snapshots):
        return None
    return snapshots[idx]

