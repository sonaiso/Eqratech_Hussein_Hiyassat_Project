from fvafk.c2b.root_resolver.wazn_adapter import WaznAdapter


def test_prefers_less_affix_heavy_long_match_for_malik():
    adapter = WaznAdapter(["مَفْعِل", "فَاعِل"])

    result = adapter.resolve("مَٰلِكِ", "مالك")

    assert result is not None
    assert result.wazn == "فَاعِل"
    assert result.root == "ملك"
    assert result.match_type == "FULLMATCH"


def test_accepts_window_match_when_fullmatch_missing():
    adapter = WaznAdapter(["فَاعِل"])

    result = adapter.resolve("بَكَاتِب", "")

    assert result is not None
    assert result.wazn == "فَاعِل"
    assert result.root == "كتب"
    assert result.match_type == "WINDOW"
    assert result.window_start == 1
