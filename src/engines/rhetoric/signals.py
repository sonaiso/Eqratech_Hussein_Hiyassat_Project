# -*- coding: utf-8 -*-
"""Rhetoric Signals V1 — signal types and trigger sets (surface/syntax-assisted)."""

from __future__ import annotations

# Signal type identifiers and Arabic labels for V1
SIGNAL_INTERROGATIVE = ("interrogative", "استفهام")
SIGNAL_VOCATIVE = ("vocative", "نداء")
SIGNAL_IMPERATIVE = ("imperative", "أمر")
SIGNAL_PROHIBITION = ("prohibition", "نهي")
SIGNAL_EMPHASIS = ("emphasis", "توكيد")
SIGNAL_EXCLUSIVITY = ("exclusivity", "قصر")
SIGNAL_OATH = ("oath", "قسم")
SIGNAL_TARAJJI = ("tarajji", "ترجّي")
SIGNAL_TAMANNI = ("tamanni", "تمنّي")

# Interrogative: هل, أ, من, ما, متى, أين, كيف, أنى, كم, أي (bare forms)
BARE_ISTIFHAM = frozenset({
    "هل", "من", "ما", "ماذا", "كيف", "أين", "متى", "كم", "أي", "أيان", "أنى",
})
# أ as hamza for question (single or with following word)
BARE_ISTIFHAM_HAMZA = "أ"

# Vocative
BARE_NIDA = frozenset({"يا", "أيا", "هيا", "وا"})

# Emphasis particles only: إنّ, أنّ, لقد (exclude إنما/لأن/كأن/لكن)
BARE_EMPHASIS = frozenset({"إن", "إنَّ", "أن", "أنَّ", "لقد"})

# Exclusivity: إنما, pattern ما ... إلا
BARE_QASR_INNAMA = frozenset({"إنما", "أنما"})
BARE_MA = "ما"
BARE_ILLA = "إلا"

# Oath
BARE_QASAM = frozenset({"والله", "بالله", "تالله", "وربي"})

# Tarajji
BARE_TARAJJI = frozenset({"لعل", "لعلَّ", "لعلي", "لعلنا", "لعلك", "لعله", "لعلها", "لعلهم", "عسى"})

# Tamanni
BARE_TAMANNI = frozenset({"ليت", "ليتما", "ليتني", "ليتنا"})

# Prohibition: لا at start
BARE_NAHY_LA = "لا"
