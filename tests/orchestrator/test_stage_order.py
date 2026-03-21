# -*- coding: utf-8 -*-
"""
Orchestrator stage ordering tests.
Stage 9: stage_order is fixed and deterministic; registry matches L0–L14.
"""

from __future__ import annotations

import pytest

from .conftest import REQUIRED_STAGE_IDS, run_pipeline_for_test


def test_stage_order_equals_required_list():
    pipeline = run_pipeline_for_test("كَاتِبٌ")
    order = pipeline.get("stage_order")
    assert order == REQUIRED_STAGE_IDS


def test_registry_order_matches_stage_order():
    from orchestrator.stage_registry import get_default_registry
    from orchestrator.types import STAGE_ORDER
    registry = get_default_registry()
    reg_ids = [s.layer_id for s in registry]
    # STAGE_ORDER may include additive layers (DEPENDENCY_SYNTAX_BUILDER, CLAUSE_ENGINE) filled in side blocks; registry is subsequence
    assert STAGE_ORDER == REQUIRED_STAGE_IDS
    order_of_reg_in_stage = [STAGE_ORDER.index(rid) for rid in reg_ids if rid in STAGE_ORDER]
    assert order_of_reg_in_stage == sorted(order_of_reg_in_stage), "registry order must preserve STAGE_ORDER subsequence"


def test_layer_outputs_keys_match_stage_order():
    pipeline = run_pipeline_for_test("إِنَّ اللَّهَ غَفُورٌ")
    order = pipeline.get("stage_order")
    lo = pipeline.get("layer_outputs") or {}
    for sid in order:
        assert sid in lo
