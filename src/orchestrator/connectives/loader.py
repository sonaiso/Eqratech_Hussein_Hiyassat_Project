# -*- coding: utf-8 -*-
"""
Load connectives from local JSON files and normalize into shared schema.
Source: data/connectives_api/ (categories 3, 18, 23, 29).
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Dict, List

from .models import CATEGORY_ID_TO_GROUP, normalized_connective

# Data dir relative to project root (or orchestrator)
def _data_dir() -> Path:
    for base in [Path.cwd(), Path(__file__).resolve().parent.parent.parent]:
        d = base / "data" / "connectives_api"
        if d.is_dir():
            return d
    return Path.cwd() / "data" / "connectives_api"

# Pass 1: only these categories
SUPPORTED_FILES = [
    ("connectives_category_3.json", 3, "أدوات الشرط"),
    ("connectives_category_18.json", 18, "أدوات النفي"),
    ("connectives_category_23.json", 23, "أدوات التفسير والتعليل"),
    ("connectives_category_29.json", 29, "أدوات الاستدراك"),
]


def _normalize_surface(s: str) -> str:
    """Strip Arabic combining diacritics for lookup. Does not change letter order."""
    if not s or not isinstance(s, str):
        return ""
    result = []
    for c in s:
        if "\u064b" <= c <= "\u0652" or c == "\u0670":
            continue
        result.append(c)
    return "".join(result).strip()


def _extract_from_item(item: Dict[str, Any], category_id: int, category_name: str, source_file: str, group: str) -> List[Dict[str, Any]]:
    """Produce one or more normalized entries from one API item (with/without harakat)."""
    out: List[Dict[str, Any]] = []
    name = (item.get("name") or "").strip()
    name_no_harakat = (item.get("name_without_harakat") or "").strip()
    tokens = []
    if name:
        tokens.append(name)
    if name_no_harakat and name_no_harakat != name:
        tokens.append(name_no_harakat)
    if not tokens:
        return out
    seen_norm = set()
    for token in tokens:
        norm = _normalize_surface(token)
        if not norm or norm in seen_norm:
            continue
        seen_norm.add(norm)
        out.append(normalized_connective(
            token=token,
            normalized_token=norm,
            category_id=category_id,
            category_name=category_name,
            group=group,
            source_file=source_file,
            raw=dict(item),
        ))
    return out


def load_connectives_from_dir(data_dir: Path | None = None) -> List[Dict[str, Any]]:
    """
    Load and normalize connectives from supported JSON files.
    Returns list of normalized connective dicts (stable schema).
    """
    data_dir = data_dir or _data_dir()
    result: List[Dict[str, Any]] = []
    for filename, category_id, category_name in SUPPORTED_FILES:
        group = CATEGORY_ID_TO_GROUP.get(category_id)
        if not group:
            continue
        path = data_dir / filename
        if not path.exists():
            continue
        try:
            with open(path, "r", encoding="utf-8") as f:
                data = json.load(f)
        except (json.JSONDecodeError, OSError):
            continue
        if not isinstance(data, dict):
            continue
        items = data.get("data")
        if not isinstance(items, list):
            continue
        for item in items:
            if not isinstance(item, dict):
                continue
            result.extend(_extract_from_item(item, category_id, category_name, filename, group))
    return result
