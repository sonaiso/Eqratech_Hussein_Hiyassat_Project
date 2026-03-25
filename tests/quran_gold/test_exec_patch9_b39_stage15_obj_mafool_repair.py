# -*- coding: utf-8 -*-
"""Master Execution Patch 9 — L17 B39: Stage15 OBJ repairs mis-tagged **فاعل** on accusative dependent."""

from __future__ import annotations

import copy

from orchestrator.l17_rule_based_i3rab import (
    _apply_b39_stage15_obj_mafool_repair,
    _get_tokens,
    _l12_features_by_token_id,
)
from orchestrator.pipeline_orchestrator import run_pipeline


def _tr(lo: dict) -> dict:
    return (lo.get("L17_RULE_BASED_I3RAB") or {}).get("transformation_result") or {}


def test_b39_repairs_fael_to_mafool_when_stage15_obj_present():
    """Minimal: verb token 0, accusative object 1 with OBJ link; wrong فاعل on dep → مفعول به."""
    r = run_pipeline("ضَرَبَ عَمْرًا")
    lo = copy.deepcopy(r["layer_outputs"])
    tr = _tr(lo)["token_reasoning"]
    tokens = _get_tokens(lo)
    l12_by_id = _l12_features_by_token_id(lo)
    dsb = [{"relation": "OBJ", "head_id": 0, "dependent_id": 1, "confidence": 0.85}]
    for e in tr:
        tid = str(e.get("token_id"))
        if tid == "1":
            e["status"] = "resolved"
            e["grammatical_family"] = "NOUN"
            e["syntactic_role"] = "فاعل"
            e["i3rab_case_or_mood"] = "مرفوع"
            e["confidence"] = 0.7
            e["gold_rule_refs"] = []
    _apply_b39_stage15_obj_mafool_repair(tr, lo, tokens, dsb, l12_by_id)
    obj = next(x for x in tr if str(x.get("token_id")) == "1")
    assert obj.get("syntactic_role") == "مفعول به"
    assert obj.get("i3rab_case_or_mood") == "منصوب"
    assert "B39_STAGE15_OBJ_MAFOOL_REPAIR" in (obj.get("gold_rule_refs") or [])
