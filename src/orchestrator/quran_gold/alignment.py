# -*- coding: utf-8 -*-
"""
Gold-word ↔ pipeline-token alignment for Quranic iʿrāb audit.

Occurrence-aware, monotonic forward matching with conservative prefix handling
(و / ف / ل / ب / ك). Ayah scope only — never crosses ayah boundaries.
"""

from __future__ import annotations

import unicodedata
from dataclasses import dataclass
from enum import Enum
from typing import List, Optional, Sequence, Tuple

# --- Legacy enum (kept for older callers) ---------------------------------
class AlignmentStatus(str, Enum):
    ALIGNED = "aligned"
    AMBIGUOUS = "alignment_ambiguous"
    NO_TOKEN = "no_matching_token"


class AlignmentOutcome(str, Enum):
    ALIGNED_UNIQUE = "aligned_unique"
    ALIGNED_BY_OCCURRENCE = "aligned_by_occurrence"
    ALIGNMENT_AMBIGUOUS = "alignment_ambiguous"
    ALIGNMENT_MISSING_IN_AYAH = "alignment_missing_in_ayah"
    ALIGNMENT_PREFIX_CONFLICT = "alignment_prefix_conflict"
    ALIGNMENT_ORDER_CONFLICT = "alignment_order_conflict"


# Single-character Arabic prefixes (base letters) attached to following word
_PREFIX_BASES = frozenset(
    {
        "\u0648",  # و
        "\u0641",  # ف
        "\u0644",  # ل
        "\u0628",  # ب
        "\u0643",  # ك
    }
)


def normalize_arabic_surface(s: str) -> str:
    """
    NFC + conservative orthographic unification for matching Quranic tokens
    across Uthmani (ٱ) vs i3rab-CSV surfaces.
    """
    t = unicodedata.normalize("NFC", (s or "").strip())
    t = t.replace("\u0671", "\u0627")  # ٱ → ا
    t = t.replace("\u0622", "\u0627").replace("\u0623", "\u0627").replace("\u0625", "\u0627")
    return t


def _first_char(s: str) -> Optional[str]:
    if not s:
        return None
    return s[0]


def _strip_leading_arabic_diacritics(s: str) -> str:
    i = 0
    while i < len(s) and ("\u064b" <= s[i] <= "\u065f" or s[i] in "\u0670\u0640"):
        i += 1
    return s[i:]


def _strip_one_leading_prefix_token_norm(token_norm: str) -> Optional[str]:
    """
    Remove at most one leading و/ف/ل/ب/ك from normalized token (base char only).
    Optionally drops a following short vowel / combining mark.
    """
    if not token_norm:
        return None
    fc = _first_char(token_norm)
    if fc in _PREFIX_BASES:
        rest = _strip_leading_arabic_diacritics(token_norm[1:])
        return rest if rest else None
    return None


def strip_match_noise(s: str) -> str:
    """Tatweel + Quranic ornaments + superscript alif (U+0670) for Uthmani vs CSV."""
    t = normalize_arabic_surface(s)
    t = t.replace("\u0640", "")
    t = t.replace("\u0670", "")  # ٰ — often present in Uthmani, absent in gold CSV
    for ch in "\u06DB\u06DA\u06D6\u06D7\u06D8\u06DE\u06E9":
        t = t.replace(ch, "")
    if t.endswith("\u0629"):
        t = t[:-1] + "\u0647"
    # CSV vs Uthmani: extra alif where Uthmani uses dagger alif (ٱ / ٰ)
    t = t.replace("عَالَم", "عَلَم")
    t = t.replace("مَالِ", "مَلِ")
    return t


def strip_weak_diacritics(s: str) -> str:
    """Remove Arabic combining marks (last-resort consonant skeleton)."""
    return "".join(c for c in s if not ("\u064b" <= c <= "\u065f"))


def match_gold_to_token_surfaces(
    gold_raw: str,
    token_raw: str,
) -> Tuple[bool, str, str, str]:
    """
    Returns (ok, reason, gold_norm, token_norm).
    reason: exact_norm | noise_stripped | token_prefix_stripped | gold_prefix_stripped | none
    """
    g = normalize_arabic_surface(gold_raw)
    t = normalize_arabic_surface(token_raw)
    gs = strip_match_noise(gold_raw)
    ts = strip_match_noise(token_raw)
    if not g:
        return False, "empty_gold", g, t
    if g == t:
        return True, "exact_norm", g, t
    if gs and ts and gs == ts:
        return True, "noise_stripped", g, t
    rest = _strip_one_leading_prefix_token_norm(t)
    if rest is not None:
        rs = strip_match_noise(rest)
        if rs == gs:
            return True, "token_prefix_stripped", g, t
    grest = _strip_one_leading_prefix_token_norm(g)
    if grest is not None:
        grs = strip_match_noise(grest)
        if grs == ts:
            return True, "gold_prefix_stripped", g, t
    if gs and ts and strip_weak_diacritics(gs) == strip_weak_diacritics(ts):
        return True, "consonant_skeleton", g, t
    return False, "none", g, t


def _gold_occurrence_index(gold_words_norm: List[str], gi: int) -> int:
    gk = gold_words_norm[gi]
    return sum(1 for j in range(gi) if gold_words_norm[j] == gk)


@dataclass(frozen=True)
class RichAlignmentResult:
    gold_index: int
    token_index: Optional[int]
    outcome: AlignmentOutcome
    reason: str
    gold_word_raw: str
    gold_word_normalized: str
    ayah_token_surface: str
    ayah_token_normalized: str
    occurrence_rank_gold: int
    occurrence_rank_ayah: int
    match_detail: str


@dataclass(frozen=True)
class AlignmentResult:
    """Per gold word index within an ayah (legacy wrapper)."""

    gold_index: int
    token_index: Optional[int]
    status: AlignmentStatus
    reason: str


def align_gold_words_to_pipeline_tokens(
    gold_words: Sequence[str],
    token_surfaces: Sequence[str],
) -> List[RichAlignmentResult]:
    """
    Occurrence-aware forward alignment of gold CSV words to pipeline token surfaces.

    - Monotonic: matched pipeline index strictly increases.
    - Same normalized gold string repeated → consume occurrences in token order.
    """
    n_g = len(gold_words)
    n_t = len(token_surfaces)
    gold_norm = [normalize_arabic_surface(g) for g in gold_words]
    results: List[RichAlignmentResult] = []
    cursor = 0

    for gi in range(n_g):
        gold_raw = gold_words[gi]
        gn = gold_norm[gi]
        if not gn:
            results.append(
                RichAlignmentResult(
                    gold_index=gi,
                    token_index=None,
                    outcome=AlignmentOutcome.ALIGNMENT_AMBIGUOUS,
                    reason="empty_gold_word",
                    gold_word_raw=gold_raw,
                    gold_word_normalized=gn,
                    ayah_token_surface="",
                    ayah_token_normalized="",
                    occurrence_rank_gold=0,
                    occurrence_rank_ayah=0,
                    match_detail="empty",
                )
            )
            continue

        occ_g = _gold_occurrence_index(gold_norm, gi)

        # All j >= cursor where gold matches token (prefix + noise rules)
        candidates: List[Tuple[int, str, str, str, str]] = []
        for j in range(cursor, n_t):
            ok, detail, g2, t2 = match_gold_to_token_surfaces(gold_raw, token_surfaces[j])
            if not ok:
                continue
            candidates.append((j, detail, g2, t2, token_surfaces[j]))

        # Order conflict: matches exist only before cursor
        if not candidates:
            any_before = False
            for j in range(0, cursor):
                ok, _, _, _ = match_gold_to_token_surfaces(gold_raw, token_surfaces[j])
                if ok:
                    any_before = True
                    break
            oc = (
                AlignmentOutcome.ALIGNMENT_ORDER_CONFLICT
                if any_before
                else AlignmentOutcome.ALIGNMENT_MISSING_IN_AYAH
            )
            results.append(
                RichAlignmentResult(
                    gold_index=gi,
                    token_index=None,
                    outcome=oc,
                    reason="no_forward_match" if not any_before else "match_only_before_cursor",
                    gold_word_raw=gold_raw,
                    gold_word_normalized=gn,
                    ayah_token_surface="",
                    ayah_token_normalized="",
                    occurrence_rank_gold=occ_g,
                    occurrence_rank_ayah=0,
                    match_detail="none",
                )
            )
            continue

        # Deduplicate by index (keep first detail)
        uniq: List[Tuple[int, str, str, str, str]] = []
        seen_j: set = set()
        for c in candidates:
            if c[0] not in seen_j:
                seen_j.add(c[0])
                uniq.append(c)

        # Greedy: take first forward match (handles repeated surfaces in order)
        j_pick, detail, g2, t2, tr = uniq[0]
        occ_rank_ayah = occ_g

        if len(uniq) == 1:
            outc = AlignmentOutcome.ALIGNED_UNIQUE
        else:
            outc = AlignmentOutcome.ALIGNED_BY_OCCURRENCE

        cursor = j_pick + 1
        results.append(
            RichAlignmentResult(
                gold_index=gi,
                token_index=j_pick,
                outcome=outc,
                reason=detail,
                gold_word_raw=gold_raw,
                gold_word_normalized=g2,
                ayah_token_surface=tr,
                ayah_token_normalized=t2,
                occurrence_rank_gold=occ_g,
                occurrence_rank_ayah=occ_rank_ayah,
                match_detail=detail,
            )
        )

    return results


def align_gold_words_to_tokens(
    gold_words: Sequence[str],
    token_surfaces: Sequence[str],
) -> Tuple[List[AlignmentResult], int, int]:
    """
    Backward-compatible wrapper. Maps rich outcomes to legacy ALIGNED / AMBIGUOUS / NO_TOKEN.
    """
    rich = align_gold_words_to_pipeline_tokens(gold_words, token_surfaces)
    legacy: List[AlignmentResult] = []
    aligned = 0
    amb = 0
    for i, r in enumerate(rich):
        if r.outcome in (AlignmentOutcome.ALIGNED_UNIQUE, AlignmentOutcome.ALIGNED_BY_OCCURRENCE):
            legacy.append(
                AlignmentResult(
                    gold_index=i,
                    token_index=r.token_index,
                    status=AlignmentStatus.ALIGNED,
                    reason=r.reason,
                )
            )
            aligned += 1
        else:
            legacy.append(
                AlignmentResult(
                    gold_index=i,
                    token_index=None,
                    status=AlignmentStatus.AMBIGUOUS
                    if r.outcome
                    in (
                        AlignmentOutcome.ALIGNMENT_AMBIGUOUS,
                        AlignmentOutcome.ALIGNMENT_PREFIX_CONFLICT,
                    )
                    else AlignmentStatus.NO_TOKEN,
                    reason=r.outcome.value,
                )
            )
            amb += 1
    return legacy, aligned, amb

