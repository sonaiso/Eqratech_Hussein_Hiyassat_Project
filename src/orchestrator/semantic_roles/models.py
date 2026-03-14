# -*- coding: utf-8 -*-
"""
Semantic role constants and confidence levels for SEMANTIC_ROLE_PROJECTION.
Structural semantic projection only — not deep semantics or logical inference.
"""

from __future__ import annotations

# Abstract semantic roles (first-scope)
ROLE_AGENT = "AGENT"
ROLE_PATIENT = "PATIENT"
ROLE_THEME = "THEME"
ROLE_EXPERIENCER = "EXPERIENCER"
ROLE_GOAL = "GOAL"
ROLE_SOURCE = "SOURCE"
ROLE_LOCATION = "LOCATION"
ROLE_INSTRUMENT = "INSTRUMENT"
ROLE_STATE = "STATE"
ROLE_UNKNOWN = "UNKNOWN"

# Projection confidence levels (assign only if >= CONF_WEAK)
CONF_STRONG = 0.85
CONF_MEDIUM = 0.65
CONF_WEAK = 0.45

# Preposition → semantic role (Rule 4) is implemented in projector via normalized lookup.
