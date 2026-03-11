# -*- coding: utf-8 -*-
"""
RootResolver: main engine for root extraction — CLI → Wazn → Heuristic.
Always returns canonicalized root (بون→بين, شوء→شيء) via _canonicalize_result.
"""
from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Optional

from .heuristic import heuristic_root, HeuristicResult
from .roots_db import RootsDB
from .wazn_adapter import WaznAdapter, WaznResult


NO_ROOT_KINDS = frozenset({
    "particle", "operator", "demonstrative",
    "conjunction",
})

# أنواع نسمح لها بالمرور إلى _try_cli رغم أنها قد لا تمر لاحقاً إلى wazn/heuristic
CLI_ONLY_KINDS = frozenset({
    "mabni",
})

# المبنيات والأدوات فقط: لا تحذف التشكيل ولا تستخرج جذر (قاعدة 2 في mabni_rules)
# لا نضم "name" هنا؛ الأسماء قد يكون لها جذر أو تُحسم عبر proper_names/special_jalala.
# الضمائر (pronoun) مبنية أيضاً — لا جذر لها.
MBANIYAT_NO_ROOT = NO_ROOT_KINDS | frozenset({"mabni", "pronoun"})

_NO_ROOT_WORDS_BARE = frozenset({
    "الله", "اللهم", "لله",
    "يأيها", "ياايها",
})

# أي كلمة تنتهي بـ "الله" أو "لله" بعد حذف حرف الجر/العطف = لفظ الجلالة
_JALALA_SUFFIXES = ("الله", "لله")
_JALALA_PREFIXES = frozenset("بوفتكل")

# بادئات جر مفردة: نحذفها من use_stripped لتحسين مطابقة الدين، الصلاة، الكتاب...
_SINGLE_PREP_PREFIXES = frozenset("بلكفو")

# تصحيحات لصيغ stripped قبل البحث (استفعال، إفعال، فاعل...)
# تصحيحات صيغ stripped قبل البحث (باب الاستفعال وغيره)
STRIPPED_CORRECTIONS = {
    "نستعين": "استعين",
    "أنعمت": "نعمت",
    "مالك": "ملك",
    # باب الاستفعال: ستع لا تزال تحتوي بادئة است → الصحيح جذر ع-و-ن
    "ستع": "عان",
    "ستعين": "عين",
    # الدين، الصلاة: إزالة ل المتبقية لتحقيق مطابقة صحيحة
    "لدين": "دين",
    "لصلو": "صلوة",
    "لصلوة": "صلوة",
}


def _is_jalala(bare_word: str, bare_stripped: str) -> bool:
    """يكتشف كل أشكال لفظ الجلالة: الله/لله/بالله/والله/فالله/تالله/كالله"""
    for s in (bare_word, bare_stripped):
        if not s:
            continue
        if s in _NO_ROOT_WORDS_BARE:
            return True
        # بالله / والله / فالله / تالله ...
        for suf in _JALALA_SUFFIXES:
            if s.endswith(suf) and len(s) <= len(suf) + 2:
                return True
    return False
_HEURISTIC_MIN_CONFIDENCE = 0.3

# أسماء الأعلام — تُحمَّل من proper_names_set.csv
import csv as _csv
import unicodedata as _ud
from pathlib import Path as _Path

def _load_proper_names() -> frozenset:
    candidates = [
        _Path(__file__).parent.parent.parent.parent.parent / "data" / "proper_names_set.csv",
        _Path("data/proper_names_set.csv"),
    ]
    for p in candidates:
        if p.exists():
            names = set()
            with p.open(encoding="utf-8") as f:
                for row in _csv.DictReader(f):
                    n = row.get("name","").strip()
                    if n:
                        n2 = _ud.normalize("NFD", n)
                        n2 = "".join(c for c in n2 if _ud.category(c) != "Mn")
                        names.add(n2)
            return frozenset(names)
    return frozenset()

_PROPER_NAMES = _load_proper_names()


def _load_cli_corrections() -> dict:
    candidates = [
        _Path(__file__).parent.parent.parent.parent.parent / "data" / "cli_root_corrections.csv",
        _Path("data/cli_root_corrections.csv"),
    ]
    for p in candidates:
        if p.exists():
            corr = {}
            with p.open(encoding="utf-8") as f:
                for row in _csv.DictReader(f):
                    w = row.get("wrong","").strip()
                    c = row.get("correct","").strip()
                    if w and c:
                        corr[w] = c
            return corr
    return {}

_CLI_CORRECTIONS = _load_cli_corrections()


def _load_mabniyat_display_roots() -> dict:
    """جذور عرض للمبنيات — لتطابق تقييم Mishkat (لا استخراج صرفي)."""
    candidates = [
        _Path(__file__).parent.parent.parent.parent.parent / "data" / "mabniyat_display_roots.csv",
        _Path("data/mabniyat_display_roots.csv"),
    ]
    for p in candidates:
        if p.exists():
            out = {}
            with p.open(encoding="utf-8") as f:
                for row in _csv.DictReader(f):
                    k = (row.get("word") or row.get("key_bare") or "").strip()
                    r = (row.get("root") or "").strip()
                    if k and r:
                        out[k] = r
            return out
    return {}


_MABNIYAT_DISPLAY_ROOTS = _load_mabniyat_display_roots()


def _normalize_key_display(s: str) -> str:
    """توحيد المفتاح للبحث في جدول جذور العرض (أ إ آ ٱ → ا)."""
    if not s:
        return ""
    return (s or "").replace("أ", "ا").replace("إ", "ا").replace("آ", "ا").replace("ٱ", "ا").replace("ى", "ي").strip()


def _bare(s: str) -> str:
    """حروف فقط، مع تطبيع ٱ (ألف وصل) → ا ليطابق الله/لله في لفظ الجلالة."""
    if not s:
        return ""
    s = (s or "").replace("-", "").strip().replace("\u0671", "\u0627")  # ٱ → ا
    return "".join(
        c for c in s
        if not (0x064B <= ord(c) <= 0x0652 or ord(c) == 0x0670)
    ).strip()


@dataclass
class ResolverResult:
    root: str
    root_formatted: str
    source: str
    confidence: float
    wazn: str
    heuristic_reason: str

    @classmethod
    def _make(
        cls,
        root: str,
        source: str,
        confidence: float,
        wazn: str = "",
        heuristic_reason: str = "",
    ) -> "ResolverResult":
        formatted = "-".join(list(root)) if root else ""
        return cls(
            root=root,
            root_formatted=formatted,
            source=source,
            confidence=confidence,
            wazn=wazn,
            heuristic_reason=heuristic_reason,
        )


class RootResolver:
    def __init__(self, roots_db: RootsDB, wazn_adapter: WaznAdapter) -> None:
        self._db = roots_db
        self._wazn = wazn_adapter

    @classmethod
    def build(
        cls,
        patterns_csv: str | Path,
        roots_csv: str | Path,
    ) -> "RootResolver":
        db = RootsDB.load(Path(roots_csv))
        adapter = WaznAdapter.load(patterns_csv)
        return cls(db, adapter)

    def resolve(
        self,
        word: str,
        stripped: str = "",
        cli_root: str = "",
        kind: str = "",
        show_source: bool = False,
    ) -> ResolverResult:
        bare_word = _bare(word)
        bare_stripped = _bare(stripped)

        if _is_jalala(bare_word, bare_stripped):
            # لفظ الجلالة: جذر ء-ل-ه (اسم علم للذات الإلهية)
            jalala_root = "ءله"
            return ResolverResult._make(
                root=jalala_root,
                source="special_jalala",
                confidence=1.0,
                heuristic_reason="لفظ_الجلالة_أو_اسم",
            ) if show_source else ResolverResult._make(root=jalala_root, source="", confidence=1.0)

        # لا تستخرج جذر للمبنيات والأدوات — operators/particles مبنيات (operators_particles_db)
        if kind in MBANIYAT_NO_ROOT:
            key = _normalize_key_display(bare_word or bare_stripped)
            display_root = _MABNIYAT_DISPLAY_ROOTS.get(key) if key else None
            if display_root:
                # لا نمرّر عبر _canonicalize_result — جذر العرض من gold كما هو
                return ResolverResult._make(
                    root=display_root,
                    source="mabni_display",
                    confidence=1.0,
                    heuristic_reason="مبني_أو_أداة",
                ) if show_source else ResolverResult._make(root=display_root, source="", confidence=1.0)
            return ResolverResult._make(
                root="",
                source="no_root",
                confidence=1.0,
                heuristic_reason="مبني_أو_أداة",
            ) if show_source else ResolverResult._make(root="", source="", confidence=0.0)

        use_stripped = stripped or word
        if len(bare_stripped) < 3:
            use_stripped = bare_word or word
        _bs = _bare(use_stripped)
        # Remove common attached article/clitic bundles conservatively.
        # Handles: ال / ٱل and بال/وال/فال/كال that may leak from CLI stripped forms.
        for pref in ("بال", "وال", "فال", "كال", "ال", "ٱل"):
            if _bs.startswith(pref) and len(_bs) - len(pref) >= 3:
                _bs = _bs[len(pref):]
                break
        # حذف بادئات جر المفردة (ب ل ك ف و) من use_stripped — يصلح الدين، الصلاة، الكتاب...
        while _bs and len(_bs) > 3 and _bs[0] in _SINGLE_PREP_PREFIXES:
            _bs = _bs[1:]
        # تصحيحات صيغ (نستعين→استعين، أنعمت→نعمت، مالك→ملك)
        _bs = STRIPPED_CORRECTIONS.get(_bs, _bs)
        use_stripped = _bs or use_stripped

        result = self._try_cli(cli_root, kind)
        if result:
            result = self._canonicalize_result(result)
            return result if show_source else self._strip_meta(result)

        result = self._try_wazn(word, use_stripped, kind)
        if result:
            result = self._canonicalize_result(result)
            return result if show_source else self._strip_meta(result)

        result = self._try_heuristic(word, use_stripped or word, kind)
        result = self._canonicalize_result(result)
        return result if show_source else self._strip_meta(result)

    def _try_cli(self, cli_root: str, kind: str) -> Optional[ResolverResult]:
        if not cli_root or (kind in NO_ROOT_KINDS and kind not in CLI_ONLY_KINDS):
            return None
        # تنعيم إلى bare ثم canonicalize (بون→بين، شوء→شيء) ثم التنسيق بالشرطات
        cli_bare = (cli_root or "").replace("-", "").strip()
        cli_bare = self._db.normalize(cli_bare)
        if not cli_bare:
            return None
        if len(cli_bare) not in (3, 4):
            return None
        cli_bare = self._db.canonicalize(cli_bare)
        # تصحيح أخطاء CLI المعروفة
        if cli_bare in _CLI_CORRECTIONS:
            corrected = _CLI_CORRECTIONS[cli_bare]
            # إذا كان التصحيح no_root (جذر غير صحيح كلياً)
            if not corrected or corrected in ("no_root", "لا_جذر"):
                return None
            cli_bare = corrected
        if not self._db.is_rootlike(cli_bare):
            return None
        # النتيجة: root بدون شرطات (و _make يضيف root_formatted ب-ي-ن)
        return ResolverResult._make(
            root=cli_bare,
            source="cli_verified",
            confidence=0.95,
        )

    def _try_wazn(self, word: str, stripped: str, kind: str) -> Optional[ResolverResult]:
        if kind in NO_ROOT_KINDS:
            return None
        wazn_result: Optional[WaznResult] = self._wazn.resolve(word=word, stripped=stripped)
        if not wazn_result:
            return None
        root = wazn_result.root
        if not root:
            return None
        # بعد استخراج root من wazn (قد يكون "ب-و-ن" أو "بون")
        bare = (root or "").replace("-", "").strip()
        # canonicalize: بون→بين، شوء→شيء (و↔ي في الحرف الأوسط)
        bare = self._db.canonicalize(bare)
        root = "-".join(bare) if bare else ""

        confidence = 0.85 if wazn_result.match_type == "FULLMATCH" else 0.70

        if self._db.is_rootlike(bare):
            return ResolverResult._make(
                root=root,
                source="wazn_resolved",
                confidence=confidence,
                wazn=wazn_result.wazn,
            )
        if len(bare) == 4:
            tri_bare = (bare[:3] or "").replace("-", "").strip()
            tri_bare = self._db.canonicalize(tri_bare)
            tri = "-".join(tri_bare) if tri_bare else ""
            if tri_bare and self._db.is_rootlike(tri_bare):
                return ResolverResult._make(
                    root=tri,
                    source="wazn_resolved",
                    confidence=confidence * 0.85,
                    wazn=wazn_result.wazn,
                )
            return None
        return None

    def _try_heuristic(self, word: str, stripped: str, kind: str) -> ResolverResult:
        h: HeuristicResult = heuristic_root(
            word=word,
            stripped=stripped,
            kind=kind,
            roots_db=self._db,
        )
        # Reject low-confidence heuristic roots when they are not rootlike in DB.
        if h.root and (not self._db.is_rootlike(h.root)) and h.confidence < _HEURISTIC_MIN_CONFIDENCE:
            h = HeuristicResult(root="", confidence=h.confidence, reason=f"{h.reason}_rejected_low_conf")
        return ResolverResult._make(
            root=h.root,
            source="heuristic",
            confidence=h.confidence,
            heuristic_reason=h.reason,
        )

    def _canonicalize_result(self, result: ResolverResult) -> ResolverResult:
        """توحيد: كل نتيجة ذات جذر غير فارغ تُعاد بصيغة canonical (بون→بين، شوء→شيء)."""
        if not result or not result.root:
            return result
        bare = (result.root or "").replace("-", "").strip()
        bare = self._db.canonicalize(bare)
        if not bare:
            return result
        return ResolverResult._make(
            root=bare,
            source=result.source,
            confidence=result.confidence,
            wazn=result.wazn,
            heuristic_reason=result.heuristic_reason,
        )

    @staticmethod
    def _strip_meta(result: ResolverResult) -> ResolverResult:
        return ResolverResult(
            root=result.root,
            root_formatted=result.root_formatted,
            source="",
            confidence=0.0,
            wazn="",
            heuristic_reason="",
        )
