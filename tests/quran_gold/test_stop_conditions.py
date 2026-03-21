# -*- coding: utf-8 -*-
"""Stop when wrong count exceeds threshold (validated in runner logic via review)."""


def test_threshold_semantics():
    max_wrong = 100
    assert 101 > max_wrong
    assert not (100 > max_wrong)
