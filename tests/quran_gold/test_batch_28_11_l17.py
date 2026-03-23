# -*- coding: utf-8 -*-
"""Batch 28.11 — Stage15 IDAFA → مضاف إليه; بسم الله fallback."""

from orchestrator.l17_rule_based_i3rab import (
    _apply_b28_11_bismillah_mudaf_ilayh,
    _build_one_token_reasoning,
    _stage15_relation_and_head,
)


def test_stage15_prefers_idafa_over_pred():
    links = [
        {"dependent_id": "1", "head_id": "0", "relation": "PRED"},
        {"dependent_id": "1", "head_id": "0", "relation": "IDAFA"},
    ]
    rel, hid = _stage15_relation_and_head("1", links)
    assert rel == "IDAFA"
    assert hid == "0"


def test_build_token_reasoning_idafa_mudaf_ilayh():
    lo = {
        "L5_WORD_TYPING": {
            "transformation_result": {
                "words": [
                    {"word": "بِسْمِ", "kind": "noun"},
                    {"word": "اللَّهِ", "kind": "noun"},
                ]
            }
        },
        "ARABIC_WORD_STATE": {"transformation_result": {"by_token_id": {}}},
    }
    ent = _build_one_token_reasoning(
        "1",
        "اللَّهِ",
        1,
        ["بِسْمِ", "اللَّهِ"],
        lo,
        None,
        "IDAFA",
        "0",
        None,
        {},
    )
    assert "مضاف" in (ent.get("syntactic_role") or "")
    assert ent.get("gold_rule_refs") == ["B28_11_IDAFA_MUDAF_ILAYH"]


def test_b28_11_bismillah_fallback_when_no_idafa_link():
    tr = [
        {
            "token_id": "0",
            "grammatical_family": "NOUN",
            "syntactic_role": "اسم مجرور",
            "status": "resolved",
            "gold_rule_refs": [],
        },
        {
            "token_id": "1",
            "grammatical_family": "NOUN",
            "syntactic_role": "خبر",
            "status": "candidate",
            "gold_rule_refs": [],
        },
    ]
    tokens = ["بِسْمِ", "اللَّهِ"]
    _apply_b28_11_bismillah_mudaf_ilayh(tr, tokens)
    assert "مضاف إليه" in (tr[1].get("syntactic_role") or "")
    assert "B28_11_BISMILLAH_MUDAF_ILAYH" in (tr[1].get("gold_rule_refs") or [])


def test_ayah_completion_ranking_builds():
    from orchestrator.quran_gold.ayah_completion_ranker import build_ranking_rows_from_snapshots

    snaps = [
        {
            "surah": 1,
            "ayah": 1,
            "decision": "PASS_STRICT",
            "truth_audit_rows": [{"audit_bucket": "ACCEPTED_STRICT_TIER"}],
            "structured_debug_rows": [],
        }
    ]
    rows = build_ranking_rows_from_snapshots(snaps)
    assert len(rows) == 1
    assert rows[0].get("surah") == 1
