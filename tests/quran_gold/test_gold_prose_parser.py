# -*- coding: utf-8 -*-
from orchestrator.quran_gold.gold_prose_parser import parse_gold_i3rab_prose


def test_mafool_bih_resolved():
    s = "مَفْعُولٌ بِهٖ مَنْصُوبٌ وَعَلَامَةُ نَصْبِهِ الْفَتْحَةُ"
    g = parse_gold_i3rab_prose(s)
    assert g.syntactic_role == "mafool_bih"
    assert g.syntactic_role_status == "resolved"
    assert g.case_bucket == "accusative"


def test_compound_prose_prefers_harf_before_late_mafool():
    s = (
        '""" الْبَاءُ """ حَرْفُ جَرٍّ مَبْنِيٌّ، وَشِبْهُ الْجُمْلَةِ فِي مَحَلِّ نَصْبٍ مَفْعُولٌ بِهِ مُقَدَّمٌ'
    )
    g = parse_gold_i3rab_prose(s)
    assert g.syntactic_role == "harf_jar"


def test_naat_resolved():
    s = "نَعْتٌ لِلْمَوْصُوفِ"
    g = parse_gold_i3rab_prose(s)
    assert g.syntactic_role == "naat"
    assert g.syntactic_role_status == "resolved"


def test_harf_particle_family():
    s = 'حَرْفُ جَرٍّ مَبْنِيٌّ عَلَى الْفَتْحِ'
    g = parse_gold_i3rab_prose(s)
    assert g.gram_family == "particle"


def test_conservative_when_no_clear_facts():
    s = "ذِكْرٌ عَامٌّ بِلَا تَفْصِيلٍ"
    g = parse_gold_i3rab_prose(s)
    assert g.syntactic_role_status in ("absent", "candidate")
    assert g.parser_confidence < 0.6
