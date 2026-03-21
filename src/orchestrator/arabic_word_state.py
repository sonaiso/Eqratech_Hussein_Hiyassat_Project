# -*- coding: utf-8 -*-
"""
Persistent Arabic word state — monotonic per-token accumulation (keyed by token_id).

Built after L9 (root + wazn from L8/L9 with stem-aware alignment). The field ``root`` is the
**canonical authoritative root** after morphology rules (e.g. hollow participle recovery in
``hollow_ism_fail`` / ``hollow_ism_mafuul``). ``raw_l8_root`` stores the L8 extractor output
before that correction when L8 provided a row (for debugging / transparency).

Downstream stages (L14, L12, L17) and presentation / Stage 15 same-root logic should use
``root`` / ``canonical_root``, not raw L8 layer rows alone. Display and tables should prefer
``canonical_root``, ``canonical_stem``, ``canonical_wazn`` when set (see ``canonical_derivation``).

See docs/stage14_jamid_mushtaq.md and docs/architecture/PIPELINE_MASTER_MEMORY.md (additive ARABIC_WORD_STATE) for the JAMID gate contract.
"""

from __future__ import annotations

import re
from copy import deepcopy
from typing import Any, Dict, List, Optional, Tuple

_DIACRITICS = re.compile(r"[\u064b-\u0652\u0670\u0640]")

# Additive layer key (not in STAGE_ORDER; stored in layer_outputs)
ARABIC_WORD_STATE_KEY = "ARABIC_WORD_STATE"
_STATE_VERSION = 2


def _normalize_surface(s: str) -> str:
    if not s or not isinstance(s, str):
        return ""
    return _DIACRITICS.sub("", (s or "").strip()).replace("\u0651", "").strip()


def strip_common_nominal_proclitics(surface: str) -> str:
    """Strip leading و/ف then ال on a diacritic-stripped form."""
    norm = _normalize_surface(surface)
    if norm.startswith(("و", "ف")) and len(norm) > 1:
        norm = norm[1:]
    if norm.startswith("ال") and len(norm) > 2:
        norm = norm[2:]
    return norm


def derivational_stem(surface: str) -> str:
    """
    Conservative stem key for derivational alignment across tokens and c2b rows.
    Strips common proclitics, definite article, typical plural / feminine suffixes.
    Result is attached to the original token as `stem` in word state.
    """
    norm = strip_common_nominal_proclitics(surface)
    changed = True
    while changed and norm:
        changed = False
        if norm.endswith("ات") and len(norm) > 5:
            norm = norm[:-2]
            changed = True
        elif norm.endswith(("ون", "ين")) and len(norm) > 4:
            norm = norm[:-2]
            changed = True
        elif norm.endswith("ان") and len(norm) > 4:
            norm = norm[:-2]
            changed = True
        elif norm.endswith("ة") and len(norm) > 3:
            norm = norm[:-1]
            changed = True
    return norm


def _root_is_present(root: Optional[str]) -> bool:
    if not root or not isinstance(root, str):
        return False
    r = root.strip()
    if not r or r in ("—", "-", "None"):
        return False
    letters = [x for x in r.replace("-", "").replace("،", "") if x.strip()]
    return len(letters) >= 2


def _wazn_is_present(template: Optional[str], word_wazn: Optional[str]) -> bool:
    for w in (template, word_wazn):
        if not w or not isinstance(w, str):
            continue
        s = _DIACRITICS.sub("", w.strip()).strip()
        if s and s not in ("", "—", "-"):
            return True
    return False


def default_word_state(token_id: str, surface: str) -> Dict[str, Any]:
    """Empty scaffold for one token (monotonic merge target)."""
    ns = _normalize_surface(surface)
    stem = derivational_stem(surface)
    return {
        "token_id": token_id,
        "surface": surface,
        "normalized_surface": ns,
        "stem": stem,
        "root": None,
        "wazn_template": None,
        "word_wazn": None,
        "derivational_class": None,
        "jamid_or_mushtaq": None,
        "gender_number": None,
        "syntax_roles": [],
        "root_confirmed": False,
        "wazn_confirmed": False,
        "root_invalidated": False,
        "wazn_invalidated": False,
        # L8 output before hollow / morphology correction (debug + transparency)
        "raw_l8_root": None,
        # e.g. hollow_ism_fail | hollow_ism_mafuul when root differs from raw_l8_root
        "root_correction_source": None,
        "hollow_ism_fail": False,
        "hollow_ism_mafuul": False,
        # Canonical derivational fields (aligned with stem after و/ف/ال + plural/fem suffix strip)
        "canonical_stem": None,
        "canonical_root": None,
        "canonical_wazn": None,
        "wazn_inference_rule": None,
    }


def _find_layer_row(
    words: List[Dict[str, Any]],
    surface: str,
    stem_key: str,
) -> Optional[Dict[str, Any]]:
    """Match c2b word row by exact surface, then by derivational stem key."""
    surface = (surface or "").strip()
    for w in words or []:
        ww = (w.get("word") or "").strip()
        if ww == surface:
            return w
    for w in words or []:
        ww = (w.get("word") or "").strip()
        if not ww:
            continue
        if derivational_stem(ww) == stem_key:
            return w
    return None


def rebuild_arabic_word_state_from_layers(lo: Dict[str, Any]) -> Dict[str, Any]:
    """
    Rebuild word state from L2 + L8 + L9 only. Call after L9.
    Does not clear additive fields if merging — use merge_monotonic_into_existing first
    when re-running in tests; pipeline calls this once after L9 on a clean slate.
    """
    tr2 = (lo.get("L2_TOKENIZATION") or {}).get("transformation_result") or {}
    tokens = tr2.get("tokens") or []
    tr8 = (lo.get("L8_ROOT_EXTRACTION") or {}).get("transformation_result") or {}
    tr9 = (lo.get("L9_WAZN_MATCHING") or {}).get("transformation_result") or {}
    tr5 = (lo.get("L5_WORD_TYPING") or {}).get("transformation_result") or {}
    words8 = tr8.get("words") or []
    words9 = tr9.get("words") or []
    words5 = tr5.get("words") or []

    by_id: Dict[str, Dict[str, Any]] = {}
    for idx, t in enumerate(tokens):
        tid = str(idx)
        surface = (t.get("word") or "").strip()
        st = default_word_state(tid, surface)
        stem_key = st["stem"]

        row5 = _find_layer_row(words5, surface, stem_key)
        kind_l5 = (row5.get("kind") or "").strip().lower() if row5 else ""

        row8 = _find_layer_row(words8, surface, stem_key)
        if row8:
            root = row8.get("root")
            if isinstance(root, dict):
                root = root.get("formatted") or ""
            root_s = (str(root).strip() if root else "") or None
            st["raw_l8_root"] = root_s
            st["root"] = root_s
            st["root_confirmed"] = _root_is_present(root_s)
            st["root_correction_source"] = None

        row9 = _find_layer_row(words9, surface, stem_key)
        if row9:
            tpl = row9.get("template")
            tpl_s = tpl.strip() if isinstance(tpl, str) else (str(tpl).strip() if tpl else "")
            ww = row9.get("word_wazn")
            ww_s = ww.strip() if isinstance(ww, str) else (str(ww).strip() if ww else "")
            st["wazn_template"] = tpl_s or None
            st["word_wazn"] = ww_s or None
            st["wazn_confirmed"] = _wazn_is_present(tpl_s, ww_s)

        # Hollow active participle (اسم فاعل أجوف): correct L8 root (e.g. ص-ي-م → ص-و-م)
        try:
            from .hollow_ism_fail import apply_hollow_root_to_word_state_entry
            apply_hollow_root_to_word_state_entry(st)
        except Exception:
            st.setdefault("hollow_ism_fail", False)

        try:
            from .hollow_ism_mafuul import apply_hollow_mafuul_root_to_word_state_entry
            apply_hollow_mafuul_root_to_word_state_entry(st)
        except Exception:
            st.setdefault("hollow_ism_mafuul", False)

        try:
            from .canonical_derivation import apply_canonical_derivation_to_word_state_entry
            apply_canonical_derivation_to_word_state_entry(st, kind_l5)
        except Exception:
            st["canonical_stem"] = st.get("stem")
            st["canonical_root"] = st.get("root")
            st["canonical_wazn"] = st.get("word_wazn") or st.get("wazn_template")

        by_id[tid] = st

    payload = {
        "status": "success",
        "by_token_id": by_id,
        "version": _STATE_VERSION,
        "source": "L2_L8_L9_rebuild",
    }
    lo[ARABIC_WORD_STATE_KEY] = {
        "layer_id": ARABIC_WORD_STATE_KEY,
        "layer_name": "Arabic word state (persistent)",
        "status": "success",
        "transformation_result": payload,
    }
    return payload


def ensure_arabic_word_state(lo: Dict[str, Any]) -> Dict[str, Any]:
    """Ensure ARABIC_WORD_STATE exists; rebuild from L8/L9 if missing."""
    existing = lo.get(ARABIC_WORD_STATE_KEY)
    tr = (existing or {}).get("transformation_result") or {}
    if tr.get("by_token_id") and tr.get("version") == _STATE_VERSION:
        return tr
    return rebuild_arabic_word_state_from_layers(lo)


def get_word_state(lo: Dict[str, Any], token_id: str) -> Dict[str, Any]:
    """Return a copy of word state for token_id, or empty dict."""
    ensure_arabic_word_state(lo)
    tr = (lo.get(ARABIC_WORD_STATE_KEY) or {}).get("transformation_result") or {}
    by_id = tr.get("by_token_id") or {}
    st = by_id.get(str(token_id))
    return deepcopy(st) if st else {}


def ref_word_state_for_token(lo: Dict[str, Any], token_id: str) -> Dict[str, Any]:
    """Live reference to word state entry (read-only use in stages); {} if missing."""
    ensure_arabic_word_state(lo)
    tr = (lo.get(ARABIC_WORD_STATE_KEY) or {}).get("transformation_result") or {}
    by_id = tr.get("by_token_id") or {}
    return by_id.get(str(token_id)) or {}


def jamid_assignment_forbidden(state: Dict[str, Any]) -> bool:
    """
    No JAMID after confirmed root or wazn unless explicitly invalidated.
    Decision: (root_confirmed ∧ ¬root_invalidated) ∨ (wazn_confirmed ∧ ¬wazn_invalidated)
    """
    rc = bool(state.get("root_confirmed")) and not bool(state.get("root_invalidated"))
    wc = bool(state.get("wazn_confirmed")) and not bool(state.get("wazn_invalidated"))
    return rc or wc


def lookup_root_wazn_from_layers(surface: str, lo: Dict[str, Any]) -> Tuple[Optional[str], Optional[str], Optional[str]]:
    """
    Stem-aware lookup: prefer ARABIC_WORD_STATE canonical root/wazn when a matching token exists;
    else L8/L9 layer rows.
    Returns (root, template, word_wazn).
    """
    ensure_arabic_word_state(lo)
    stem_key = derivational_stem(surface)
    tr2 = (lo.get("L2_TOKENIZATION") or {}).get("transformation_result") or {}
    tokens = tr2.get("tokens") or []
    trs = (lo.get(ARABIC_WORD_STATE_KEY) or {}).get("transformation_result") or {}
    by_id = trs.get("by_token_id") or {}
    for idx, t in enumerate(tokens):
        tw = (t.get("word") or "").strip()
        if not tw:
            continue
        if tw == surface.strip() or derivational_stem(tw) == stem_key:
            ws = by_id.get(str(idx)) or {}
            r = ws.get("canonical_root") or ws.get("root")
            tpl = ws.get("wazn_template")
            ww = ws.get("canonical_wazn") or ws.get("word_wazn")
            cwonly = ws.get("canonical_wazn")
            if _root_is_present(r) or _wazn_is_present(tpl, ww) or _wazn_is_present(cwonly, None):
                return (
                    (str(r).strip() if r else None) or None,
                    (str(tpl).strip() if tpl else None) or None,
                    (str(ww).strip() if ww else None) or None,
                )
            break

    tr8 = (lo.get("L8_ROOT_EXTRACTION") or {}).get("transformation_result") or {}
    tr9 = (lo.get("L9_WAZN_MATCHING") or {}).get("transformation_result") or {}
    row8 = _find_layer_row(tr8.get("words") or [], surface, stem_key)
    root: Optional[str] = None
    if row8:
        r = row8.get("root")
        if isinstance(r, dict):
            r = r.get("formatted") or ""
        root = (str(r).strip() if r else "") or None
    row9 = _find_layer_row(tr9.get("words") or [], surface, stem_key)
    template: Optional[str] = None
    word_wazn: Optional[str] = None
    if row9:
        tpl = row9.get("template")
        template = tpl.strip() if isinstance(tpl, str) else (str(tpl).strip() if tpl else "") or None
        ww = row9.get("word_wazn")
        word_wazn = ww.strip() if isinstance(ww, str) else (str(ww).strip() if ww else "") or None
    return root, template, word_wazn


def build_root_wazn_display_rows(lo: Dict[str, Any]) -> List[Dict[str, Any]]:
    """
    Per-token rows for root/wazn tables and tests: canonical root from ARABIC_WORD_STATE
    (post hollow correction), not raw L8 alone.
    """
    ensure_arabic_word_state(lo)
    tr2 = (lo.get("L2_TOKENIZATION") or {}).get("transformation_result") or {}
    tokens = tr2.get("tokens") or []
    trs = (lo.get(ARABIC_WORD_STATE_KEY) or {}).get("transformation_result") or {}
    by_id = trs.get("by_token_id") or {}
    rows: List[Dict[str, Any]] = []
    for i, t in enumerate(tokens):
        surf = (t.get("word") or "").strip()
        ws = by_id.get(str(i)) or {}
        rows.append(
            {
                "token_id": str(i),
                "surface": surf,
                "root": (ws.get("canonical_root") or ws.get("root") or "").strip() or None,
                "canonical_stem": ws.get("canonical_stem"),
                "canonical_wazn": ws.get("canonical_wazn"),
                "raw_l8_root": ws.get("raw_l8_root"),
                "wazn_template": ws.get("wazn_template"),
                "word_wazn": ws.get("word_wazn"),
                "derivational_class": ws.get("derivational_class"),
                "root_correction_source": ws.get("root_correction_source"),
            }
        )
    return rows


def compact_roots_summary_first_n(lo: Dict[str, Any], n: int = 5) -> str:
    """Short 'surface: root' line for L14 compact mode (canonical roots)."""
    ensure_arabic_word_state(lo)
    tr2 = (lo.get("L2_TOKENIZATION") or {}).get("transformation_result") or {}
    tokens = tr2.get("tokens") or []
    trs = (lo.get(ARABIC_WORD_STATE_KEY) or {}).get("transformation_result") or {}
    by_id = trs.get("by_token_id") or {}
    parts: List[str] = []
    for i, t in enumerate(tokens[: max(0, n)]):
        surf = (t.get("word") or "").strip()
        ws = by_id.get(str(i)) or {}
        r = ws.get("canonical_root") or ws.get("root") or "—"
        parts.append(f"{surf}: {r}")
    return "; ".join(parts) if parts else "—"


def build_detailed_morphology_roots_and_wazn(lo: Dict[str, Any]) -> Tuple[str, str]:
    """
    Detailed L14 morphology strings: canonical roots from ARABIC_WORD_STATE; wazn from state with L9 fallback.
    """
    ensure_arabic_word_state(lo)
    tr2 = (lo.get("L2_TOKENIZATION") or {}).get("transformation_result") or {}
    tokens = tr2.get("tokens") or []
    trs = (lo.get(ARABIC_WORD_STATE_KEY) or {}).get("transformation_result") or {}
    by_id = trs.get("by_token_id") or {}
    tr9 = (lo.get("L9_WAZN_MATCHING") or {}).get("transformation_result") or {}
    words9 = tr9.get("words") or []

    root_lines: List[str] = []
    for i, t in enumerate(tokens):
        surf = (t.get("word") or "").strip()
        ws = by_id.get(str(i)) or {}
        canon = ws.get("canonical_root") or ws.get("root") or "—"
        raw = ws.get("raw_l8_root")
        if raw and isinstance(raw, str) and raw.strip() and raw.strip() != (canon or ""):
            root_lines.append(f"  {surf}: {canon}  (L8 raw: {raw.strip()})")
        else:
            root_lines.append(f"  {surf}: {canon}")

    roots_block = (
        "Canonical roots (ARABIC_WORD_STATE — authoritative for downstream):\n" + "\n".join(root_lines)
        if root_lines
        else "Morphology: no tokens."
    )

    wazn_lines: List[str] = []
    for i, t in enumerate(tokens):
        surf = (t.get("word") or "").strip()
        ws = by_id.get(str(i)) or {}
        tpl = (ws.get("wazn_template") or "").strip()
        ww = (ws.get("word_wazn") or "").strip()
        cwz = (ws.get("canonical_wazn") or "").strip()
        wz = cwz or tpl or ww
        if not wz:
            row9 = _find_layer_row(words9, surf, derivational_stem(surf))
            if row9:
                wz = (row9.get("template") or row9.get("word_wazn") or "").strip() or "—"
            else:
                wz = "—"
        wazn_lines.append(f"  {surf}: {wz}")

    wazn_block = "\n".join(wazn_lines) if wazn_lines else "  (none)"
    return roots_block, wazn_block


def merge_l14_classifications_into_word_state(lo: Dict[str, Any], l14_tr: Dict[str, Any]) -> None:
    """Patch derivational_class / jamid_or_mushtaq / canonical root from L14 output (monotonic)."""
    ensure_arabic_word_state(lo)
    wrapper = lo.setdefault(ARABIC_WORD_STATE_KEY, {})
    tr = wrapper.setdefault("transformation_result", {})
    by_id: Dict[str, Dict[str, Any]] = tr.setdefault("by_token_id", {})
    for tc in (l14_tr or {}).get("token_classifications") or []:
        tid = str(tc.get("token_id"))
        if tid not in by_id:
            continue
        st = by_id[tid]
        if tc.get("derivational_class") is not None:
            st["derivational_class"] = tc.get("derivational_class")
        if tc.get("jamid_or_mushtaq") is not None:
            st["jamid_or_mushtaq"] = tc.get("jamid_or_mushtaq")
        # Authoritative display root: L14 classification already uses hollow-resolved roots
        nr = tc.get("root")
        if isinstance(nr, str) and nr.strip():
            st["root"] = nr.strip()
            st["canonical_root"] = nr.strip()
            letters = [x for x in st["root"].replace("-", "").replace("،", "") if x.strip()]
            st["root_confirmed"] = len(letters) >= 2
        nw = tc.get("wazn")
        if isinstance(nw, str) and nw.strip():
            st["canonical_wazn"] = nw.strip()
            st["wazn_template"] = nw.strip()
            st["word_wazn"] = nw.strip()
            st["wazn_confirmed"] = True
    tr["source"] = "L2_L8_L9_L14_merged"


def merge_l12_gender_number_into_word_state(lo: Dict[str, Any], l12_tr: Dict[str, Any]) -> None:
    """Attach L12 gender/number features without dropping morphology fields."""
    ensure_arabic_word_state(lo)
    wrapper = lo.setdefault(ARABIC_WORD_STATE_KEY, {})
    tr = wrapper.setdefault("transformation_result", {})
    by_id: Dict[str, Dict[str, Any]] = tr.setdefault("by_token_id", {})
    for f in (l12_tr or {}).get("token_features") or []:
        tid = str(f.get("token_id"))
        if tid not in by_id:
            continue
        by_id[tid]["gender_number"] = {
            "gender": f.get("gender"),
            "number": f.get("number"),
            "number_type": f.get("number_type"),
            "gender_rule": f.get("gender_rule"),
            "number_rule": f.get("number_rule"),
        }
    tr["source"] = "L2_L8_L9_L14_L12_merged"
