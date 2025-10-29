import hashlib
import unicodedata

from hypothesis import given, settings
from hypothesis.strategies import text


def _build_arabic_alphabet() -> str:
    """Assemble a Unicode alphabet that covers common Arabic code point ranges."""
    ranges = [
        (0x0600, 0x06FF),  # Arabic
        (0x0750, 0x077F),  # Arabic Supplement
        (0x08A0, 0x08FF),  # Arabic Extended-A
    ]
    extras = [0x200C, 0x200D]  # zero-width joiners that appear in real data
    codepoints = set()
    for start, end in ranges:
        codepoints.update(range(start, end + 1))
    codepoints.update(extras)
    return "".join(chr(cp) for cp in sorted(codepoints))


ARABIC_ALPHABET = _build_arabic_alphabet()
MAX_SAMPLE_SIZE = 32


@settings(deadline=None)
@given(text(alphabet=ARABIC_ALPHABET, min_size=0, max_size=MAX_SAMPLE_SIZE))
def test_nfc_is_idempotent(arabic_text: str) -> None:
    """NFC normalization should be stable on repeated application."""
    nfc_once = unicodedata.normalize("NFC", arabic_text)
    nfc_twice = unicodedata.normalize("NFC", nfc_once)
    assert nfc_twice == nfc_once


@settings(deadline=None)
@given(text(alphabet=ARABIC_ALPHABET, min_size=0, max_size=MAX_SAMPLE_SIZE))
def test_nfd_round_trip_preserves_structure(arabic_text: str) -> None:
    """An NFC->NFD->NFC cycle should return to an equivalent representation."""
    nfd = unicodedata.normalize("NFD", arabic_text)
    round_tripped = unicodedata.normalize("NFC", nfd)
    rebuilt = unicodedata.normalize("NFD", round_tripped)
    assert rebuilt == nfd


@settings(deadline=None)
@given(text(alphabet=ARABIC_ALPHABET, min_size=0, max_size=MAX_SAMPLE_SIZE))
def test_sha256_digest_remains_stable(arabic_text: str) -> None:
    """Hashing after normalization should remain consistent across forms."""
    baseline = unicodedata.normalize("NFC", arabic_text)
    digest = hashlib.sha256(baseline.encode("utf-8")).hexdigest()
    variant = unicodedata.normalize("NFC", unicodedata.normalize("NFD", arabic_text))
    variant_digest = hashlib.sha256(variant.encode("utf-8")).hexdigest()
    assert variant_digest == digest
