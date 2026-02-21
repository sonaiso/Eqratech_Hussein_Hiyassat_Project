"""Syntax package - I3rab and syntax analysis."""

from .models import (
    I3rabAnnotation,
    I3rabComponents,
    SyntaxFeatures,
)

from .mappings import (
    I3RAB_TYPE_AR_TO_EN,
    CASE_AR_TO_EN,
    CASE_MARKER_AR_TO_EN,
    map_i3rab_to_role,
    map_ar_to_en,
)

__all__ = [
    "I3rabAnnotation",
    "I3rabComponents",
    "SyntaxFeatures",
    "I3RAB_TYPE_AR_TO_EN",
    "CASE_AR_TO_EN",
    "CASE_MARKER_AR_TO_EN",
    "map_i3rab_to_role",
    "map_ar_to_en",
]
"""Syntax package - I3rab and syntax analysis."""

from .models import (
    I3rabAnnotation,
    I3rabComponents,
    SyntaxFeatures,
)

from .mappings import (
    I3RAB_TYPE_AR_TO_EN,
    CASE_AR_TO_EN,
    CASE_MARKER_AR_TO_EN,
    map_i3rab_to_role,
    map_ar_to_en,
)

from .i3rab_parser import (
    I3rabParser,
    parse_i3rab,
)

__all__ = [
    "I3rabAnnotation",
    "I3rabComponents",
    "SyntaxFeatures",
    "I3RAB_TYPE_AR_TO_EN",
    "CASE_AR_TO_EN",
    "CASE_MARKER_AR_TO_EN",
    "map_i3rab_to_role",
    "map_ar_to_en",
    "I3rabParser",
    "parse_i3rab",
]