# -*- coding: utf-8 -*-
"""
i3rab_generator.py
==================
يولد العبارة الإعرابية الكاملة برمجياً بدل قاموس ضخم.
المدخلات: (وظيفة نحوية، نوع كلمة، إعراب، عدد، جنس، تعريف، ...)
المخرج: عبارة إعرابية كاملة بالتشكيل الكامل
"""
from __future__ import annotations
from enum import Enum
from dataclasses import dataclass
from typing import Optional

# ======================================================
# 1. المعطيات الأساسية
# ======================================================

class Case(str, Enum):
    RAFA  = "رفع"
    NASB  = "نصب"
    JARR  = "جر"
    JAZM  = "جزم"

class Number(str, Enum):
    MUFRAD  = "مفرد"
    MUTHANA = "مثنى"
    JAMA3   = "جمع"
    JAMA3_M = "جمع_مذكر_سالم"
    JAMA3_F = "جمع_مؤنث_سالم"

class Gender(str, Enum):
    M = "مذكر"
    F = "مؤنث"

class WordType(str, Enum):
    NOUN      = "اسم"
    VERB_PAST = "فعل_ماضٍ"
    VERB_MUD  = "فعل_مضارع"
    VERB_AMR  = "فعل_أمر"
    PARTICLE  = "حرف"
    PRONOUN   = "ضمير"

class Function(str, Enum):
    FA3IL       = "فاعل"
    NAIB_FA3IL  = "نائب_فاعل"
    MAFOOL      = "مفعول_به"
    MAFOOL2     = "مفعول_به_ثانٍ"
    MUBTADA     = "مبتدأ"
    KHABAR      = "خبر"
    MUBTADA_MU  = "مبتدأ_مؤخر"
    KHABAR_MU   = "خبر_مقدم"
    ISM_KANA    = "اسم_كان"
    KHABAR_KANA = "خبر_كان"
    ISM_INNA    = "اسم_إن"
    KHABAR_INNA = "خبر_إن"
    MUDAF_ILAY  = "مضاف_إليه"
    NA3T        = "نعت"
    TAWKID      = "توكيد"
    BADAL       = "بدل"
    ATF         = "معطوف"
    ZARFM       = "ظرف_مكان"
    ZARFZ       = "ظرف_زمان"
    ISM_MAJRUR  = "اسم_مجرور"
    HAL         = "حال"
    TAMYIZ      = "تمييز"
    MAFOOL_MUTLAQ = "مفعول_مطلق"

# ======================================================
# 2. علامات الإعراب
# ======================================================

def get_sign(case: Case, number: Number, gender: Gender,
             is_verb: bool = False, is_af3al_khamsa: bool = False,
             is_mamnou3: bool = False, is_asma_khamsa: bool = False,
             is_maqsur: bool = False, is_manqus: bool = False) -> str:
    """
    يرجع علامة الإعراب الصحيحة حسب الحالة والعدد والجنس.
    """
    # أفعال الخمسة
    if is_verb and is_af3al_khamsa:
        if case == Case.RAFA:
            return "ثُبُوتُ النُّونِ لِأَنَّهُ مِنَ الْأَفْعَالِ الْخَمْسَةِ"
        if case in (Case.NASB, Case.JAZM):
            return "حَذْفُ النُّونِ لِأَنَّهُ مِنَ الْأَفْعَالِ الْخَمْسَةِ"

    # فعل مضارع عادي
    if is_verb and case == Case.JAZM:
        return "حَذْفُ حَرْفِ الْعِلَّةِ" if is_manqus else "السُّكُونُ الظَّاهِرُ"

    # مقصور
    if is_maqsur:
        signs = {Case.RAFA: "الضَّمَّةُ الْمُقَدَّرَةُ لِلتَّعَذُّرِ",
                 Case.NASB: "الْفَتْحَةُ الْمُقَدَّرَةُ لِلتَّعَذُّرِ",
                 Case.JARR: "الْكَسْرَةُ الْمُقَدَّرَةُ لِلتَّعَذُّرِ"}
        return signs[case]

    # منقوص
    if is_manqus and not is_verb:
        signs = {Case.RAFA: "الضَّمَّةُ الْمُقَدَّرَةُ لِلثِّقَلِ",
                 Case.NASB: "الْفَتْحَةُ الظَّاهِرَةُ",
                 Case.JARR: "الْكَسْرَةُ الْمُقَدَّرَةُ لِلثِّقَلِ"}
        return signs[case]

    # مثنى
    if number == Number.MUTHANA:
        if case == Case.RAFA:
            return "الْأَلِفُ لِأَنَّهُ مُثَنًّى"
        return "الْيَاءُ لِأَنَّهُ مُثَنًّى"

    # جمع مذكر سالم
    if number == Number.JAMA3_M:
        if case == Case.RAFA:
            return "الْوَاوُ لِأَنَّهُ جَمْعُ مُذَكَّرٍ سَالِمٌ"
        return "الْيَاءُ لِأَنَّهُ جَمْعُ مُذَكَّرٍ سَالِمٌ"

    # جمع مؤنث سالم
    if number == Number.JAMA3_F:
        if case == Case.RAFA:
            return "الضَّمَّةُ الظَّاهِرَةُ"
        if case == Case.NASB:
            return "الْكَسْرَةُ الظَّاهِرَةُ لِأَنَّهُ جَمْعُ مُؤَنَّثٍ سَالِمٌ"
        return "الْكَسْرَةُ الظَّاهِرَةُ لِأَنَّهُ جَمْعُ مُؤَنَّثٍ سَالِمٌ"

    # أسماء الخمسة
    if is_asma_khamsa:
        if case == Case.RAFA:
            return "الْوَاوُ لِأَنَّهُ مِنَ الْأَسْمَاءِ الْخَمْسَةِ"
        if case == Case.NASB:
            return "الْأَلِفُ لِأَنَّهُ مِنَ الْأَسْمَاءِ الْخَمْسَةِ"
        return "الْيَاءُ لِأَنَّهُ مِنَ الْأَسْمَاءِ الْخَمْسَةِ"

    # ممنوع من الصرف
    if is_mamnou3:
        if case == Case.RAFA:
            return "الضَّمَّةُ الظَّاهِرَةُ"
        if case == Case.NASB:
            return "الْفَتْحَةُ الظَّاهِرَةُ"
        return "الْفَتْحَةُ الظَّاهِرَةُ لِأَنَّهُ مَمْنُوعٌ مِنَ الصَّرْفِ"

    # المعرب العادي
    TABLE = {
        Case.RAFA: "الضَّمَّةُ الظَّاهِرَةُ",
        Case.NASB: "الْفَتْحَةُ الظَّاهِرَةُ",
        Case.JARR: "الْكَسْرَةُ الظَّاهِرَةُ",
        Case.JAZM: "السُّكُونُ الظَّاهِرُ",
    }
    return TABLE[case]

# ======================================================
# 3. نص الإعراب لكل حالة
# ======================================================

CASE_WORD = {
    Case.RAFA: ("مَرْفُوعٌ", "رَفْعِهِ"),
    Case.NASB: ("مَنْصُوبٌ", "نَصْبِهِ"),
    Case.JARR: ("مَجْرُورٌ", "جَرِّهِ"),
    Case.JAZM: ("مَجْزُومٌ", "جَزْمِهِ"),
}

FUNC_TEXT = {
    Function.FA3IL:       "فَاعِلٌ",
    Function.NAIB_FA3IL:  "نَائِبُ فَاعِلٍ",
    Function.MAFOOL:      "مَفْعُولٌ بِهِ",
    Function.MAFOOL2:     "مَفْعُولٌ بِهِ ثَانٍ",
    Function.MUBTADA:     "مُبْتَدَأٌ",
    Function.KHABAR:      "خَبَرٌ",
    Function.MUBTADA_MU:  "مُبْتَدَأٌ مُؤَخَّرٌ",
    Function.KHABAR_MU:   "خَبَرٌ مُقَدَّمٌ",
    Function.ISM_KANA:    "اسْمُ كَانَ",
    Function.KHABAR_KANA: "خَبَرُ كَانَ",
    Function.ISM_INNA:    "اسْمُ إِنَّ",
    Function.KHABAR_INNA: "خَبَرُ إِنَّ",
    Function.MUDAF_ILAY:  "مُضَافٌ إِلَيْهِ",
    Function.NA3T:        "نَعْتٌ",
    Function.TAWKID:      "تَوْكِيدٌ",
    Function.BADAL:       "بَدَلٌ",
    Function.ATF:         "مَعْطُوفٌ",
    Function.ZARFM:       "ظَرْفُ مَكَانٍ",
    Function.ZARFZ:       "ظَرْفُ زَمَانٍ",
    Function.ISM_MAJRUR:  "اسْمٌ",
    Function.HAL:         "حَالٌ",
    Function.TAMYIZ:      "تَمْيِيزٌ",
    Function.MAFOOL_MUTLAQ: "مَفْعُولٌ مُطْلَقٌ",
}

# الوظائف التي تُرفع / تُنصب / تُجر
FUNC_DEFAULT_CASE = {
    Function.FA3IL:       Case.RAFA,
    Function.NAIB_FA3IL:  Case.RAFA,
    Function.MUBTADA:     Case.RAFA,
    Function.KHABAR:      Case.RAFA,
    Function.MUBTADA_MU:  Case.RAFA,
    Function.KHABAR_MU:   Case.RAFA,
    Function.MAFOOL:      Case.NASB,
    Function.MAFOOL2:     Case.NASB,
    Function.ISM_KANA:    Case.RAFA,
    Function.KHABAR_KANA: Case.NASB,
    Function.ISM_INNA:    Case.NASB,
    Function.KHABAR_INNA: Case.RAFA,
    Function.MUDAF_ILAY:  Case.JARR,
    Function.NA3T:        None,  # يتبع المنعوت
    Function.TAWKID:      None,
    Function.BADAL:        None,
    Function.ATF:          None,
    Function.ZARFM:        Case.NASB,
    Function.ZARFZ:        Case.NASB,
    Function.ISM_MAJRUR:  Case.JARR,
    Function.HAL:         Case.NASB,
    Function.TAMYIZ:      Case.NASB,
    Function.MAFOOL_MUTLAQ: Case.NASB,
}

# ======================================================
# 4. بناء العبارة الإعرابية
# ======================================================

@dataclass
class WordInfo:
    word_type: WordType
    function: Function
    case: Optional[Case] = None           # إن كان None يُستنتج من الوظيفة
    number: Number = Number.MUFRAD
    gender: Gender = Gender.M
    is_definite: bool = False
    is_af3al_khamsa: bool = False
    is_mamnou3: bool = False
    is_asma_khamsa: bool = False
    is_maqsur: bool = False
    is_manqus: bool = False
    verb_bina: str = "الْفَتْحِ"          # للفعل الماضي: الفتح / الضم / السكون
    mudari3_suffix: Optional[str] = None  # واو الجماعة / ألف الاثنين / نون النسوة


def generate_i3rab(info: WordInfo) -> str:
    """
    يولد العبارة الإعرابية الكاملة.
    """
    wt = info.word_type
    fn = info.function

    # --- فعل ماضٍ ---
    if wt == WordType.VERB_PAST:
        base = f"فِعْلٌ مَاضٍ مَبْنِيٌّ عَلَى {info.verb_bina}"
        if info.mudari3_suffix:
            base += f" لِاتِّصَالِهِ بِ{info.mudari3_suffix}"
        return base

    # --- فعل أمر ---
    if wt == WordType.VERB_AMR:
        if info.is_af3al_khamsa:
            return "فِعْلُ أَمْرٍ مَبْنِيٌّ عَلَى حَذْفِ النُّونِ"
        return "فِعْلُ أَمْرٍ مَبْنِيٌّ عَلَى السُّكُونِ"

    # --- فعل مضارع ---
    if wt == WordType.VERB_MUD:
        case = info.case or Case.RAFA
        case_word, case_of = CASE_WORD[case]
        sign = get_sign(case, info.number, info.gender,
                        is_verb=True,
                        is_af3al_khamsa=info.is_af3al_khamsa,
                        is_manqus=info.is_manqus)
        return f"فِعْلٌ مُضَارِعٌ {case_word} وَعَلَامَةُ {case_of} {sign}"

    # --- حرف ---
    if wt == WordType.PARTICLE:
        # الحروف مبنية — نُرجع فقط نوع الحرف
        # هذا يُعالج في قاموس الحروف الثابت
        return _particle_i3rab(info)

    # --- اسم / ضمير ---
    case = info.case or FUNC_DEFAULT_CASE.get(fn) or Case.RAFA
    case_word, case_of = CASE_WORD[case]
    sign = get_sign(case, info.number, info.gender,
                    is_mamnou3=info.is_mamnou3,
                    is_asma_khamsa=info.is_asma_khamsa,
                    is_maqsur=info.is_maqsur,
                    is_manqus=info.is_manqus)

    func_text = FUNC_TEXT.get(fn, "")

    # مضاف إليه وظرف لا يحتاج وظيفة نحوية + إعراب منفصل
    if fn == Function.MUDAF_ILAY:
        return f"مُضَافٌ إِلَيْهِ {case_word} وَعَلَامَةُ {case_of} {sign}"

    if fn == Function.ISM_MAJRUR:
        return f"اسْمٌ {case_word} وَعَلَامَةُ {case_of} {sign}"

    if fn in (Function.ZARFM, Function.ZARFZ):
        zarftype = "مَكَانٍ" if fn == Function.ZARFM else "زَمَانٍ"
        return f"ظَرْفُ {zarftype} {case_word} وَعَلَامَةُ {case_of} {sign}"

    # الوظائف العادية
    return f"{func_text} {case_word} وَعَلَامَةُ {case_of} {sign}"


# ======================================================
# 5. قاموس الحروف الثابت (مبني)
# ======================================================

PARTICLES = {
    "وَ":   "الْوَاوُ حَرْفُ عَطْفٍ مَبْنِيٌّ عَلَى الْفَتْحِ",
    "فَ":   "الْفَاءُ حَرْفُ عَطْفٍ مَبْنِيٌّ عَلَى الْفَتْحِ",
    "ثُمَّ":"ثُمَّ حَرْفُ عَطْفٍ مَبْنِيٌّ عَلَى الْفَتْحِ",
    "بِ":   "الْبَاءُ حَرْفُ جَرٍّ مَبْنِيٌّ عَلَى الْكَسْرِ",
    "لِ":   "اللَّامُ حَرْفُ جَرٍّ مَبْنِيٌّ عَلَى الْكَسْرِ",
    "مِنْ": "مِنْ حَرْفُ جَرٍّ مَبْنِيٌّ عَلَى السُّكُونِ",
    "إِلَى":"إِلَى حَرْفُ جَرٍّ مَبْنِيٌّ عَلَى السُّكُونِ",
    "عَلَى":"عَلَى حَرْفُ جَرٍّ مَبْنِيٌّ عَلَى السُّكُونِ",
    "عَنْ": "عَنْ حَرْفُ جَرٍّ مَبْنِيٌّ عَلَى السُّكُونِ",
    "فِي":  "فِي حَرْفُ جَرٍّ مَبْنِيٌّ عَلَى السُّكُونِ",
    "إِنَّ":"إِنَّ حَرْفُ تَوْكِيدٍ وَنَصْبٍ مَبْنِيٌّ عَلَى الْفَتْحِ",
    "أَنَّ":"أَنَّ حَرْفُ تَوْكِيدٍ وَنَصْبٍ مَبْنِيٌّ عَلَى الْفَتْحِ",
    "لَا":  "لَا حَرْفُ نَفْيٍ مَبْنِيٌّ عَلَى السُّكُونِ",
    "لَمْ": "لَمْ حَرْفُ نَفْيٍ وَجَزْمٍ مَبْنِيٌّ عَلَى السُّكُونِ",
    "لَنْ": "لَنْ حَرْفُ نَفْيٍ وَنَصْبٍ مَبْنِيٌّ عَلَى السُّكُونِ",
    "قَدْ": "قَدْ حَرْفُ تَحْقِيقٍ مَبْنِيٌّ عَلَى السُّكُونِ",
    "هَلْ": "هَلْ حَرْفُ اسْتِفْهَامٍ مَبْنِيٌّ عَلَى السُّكُونِ",
    "أَ":   "الْهَمْزَةُ حَرْفُ اسْتِفْهَامٍ مَبْنِيٌّ عَلَى الْفَتْحِ",
    "إِنْ": "إِنْ حَرْفُ شَرْطٍ مَبْنِيٌّ عَلَى السُّكُونِ",
    "لَوْ": "لَوْ حَرْفُ شَرْطٍ مَبْنِيٌّ عَلَى السُّكُونِ",
}

def _particle_i3rab(info: WordInfo) -> str:
    return "حَرْفٌ مَبْنِيٌّ"


# ======================================================
# 6. اختبار
# ======================================================

if __name__ == "__main__":
    tests = [
        # فاعل مرفوع مفرد
        WordInfo(WordType.NOUN, Function.FA3IL),
        # مفعول به منصوب جمع مذكر سالم
        WordInfo(WordType.NOUN, Function.MAFOOL, number=Number.JAMA3_M),
        # مضاف إليه مجرور مفرد مقصور
        WordInfo(WordType.NOUN, Function.MUDAF_ILAY, is_maqsur=True),
        # اسم مجرور مثنى
        WordInfo(WordType.NOUN, Function.ISM_MAJRUR, number=Number.MUTHANA),
        # نعت منصوب ممنوع من الصرف
        WordInfo(WordType.NOUN, Function.NA3T, case=Case.NASB, is_mamnou3=True),
        # فعل مضارع مرفوع أفعال الخمسة
        WordInfo(WordType.VERB_MUD, Function.FA3IL, is_af3al_khamsa=True),
        # فعل مضارع مجزوم
        WordInfo(WordType.VERB_MUD, Function.FA3IL, case=Case.JAZM),
        # فعل ماضٍ + واو الجماعة
        WordInfo(WordType.VERB_PAST, Function.FA3IL,
                 verb_bina="الضَّمِّ", mudari3_suffix="وَاوِ الْجَمَاعَةِ"),
        # فعل أمر أفعال الخمسة
        WordInfo(WordType.VERB_AMR, Function.FA3IL, is_af3al_khamsa=True),
        # خبر إن مرفوع جمع مؤنث سالم
        WordInfo(WordType.NOUN, Function.KHABAR_INNA, number=Number.JAMA3_F),
        # ظرف مكان
        WordInfo(WordType.NOUN, Function.ZARFM),
        # حال منصوب منقوص
        WordInfo(WordType.NOUN, Function.HAL, is_manqus=True),
    ]

    print("=== اختبار المولّد الإعرابي ===\n")
    for i, info in enumerate(tests, 1):
        result = generate_i3rab(info)
        fn = FUNC_TEXT.get(info.function, info.function.value)
        print(f"{i:2}. [{fn}] → {result}")
