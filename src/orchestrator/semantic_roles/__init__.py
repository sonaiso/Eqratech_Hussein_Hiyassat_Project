# -*- coding: utf-8 -*-
"""
SEMANTIC_ROLE_PROJECTION — additive enrichment layer mapping syntactic roles
and valency into abstract semantic roles. Does not modify syntax, i'rab, or validation.
"""

from __future__ import annotations

from .models import (
    CONF_MEDIUM,
    CONF_STRONG,
    CONF_WEAK,
    ROLE_AGENT,
    ROLE_EXPERIENCER,
    ROLE_GOAL,
    ROLE_INSTRUMENT,
    ROLE_LOCATION,
    ROLE_PATIENT,
    ROLE_SOURCE,
    ROLE_STATE,
    ROLE_THEME,
    ROLE_UNKNOWN,
)
from .projector import project_semantic_roles

__all__ = [
    "project_semantic_roles",
    "ROLE_AGENT",
    "ROLE_PATIENT",
    "ROLE_THEME",
    "ROLE_EXPERIENCER",
    "ROLE_GOAL",
    "ROLE_SOURCE",
    "ROLE_LOCATION",
    "ROLE_INSTRUMENT",
    "ROLE_STATE",
    "ROLE_UNKNOWN",
    "CONF_STRONG",
    "CONF_MEDIUM",
    "CONF_WEAK",
]
