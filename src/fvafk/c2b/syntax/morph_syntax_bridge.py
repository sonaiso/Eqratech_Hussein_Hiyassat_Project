"""Morph-Syntax Bridge - Infer syntax from morphology features.

Connects morphology layer (Sprint 3) to syntax layer (Sprint 4).
Uses rule-based inference with context awareness.

Author: Hussein Hiyassat
Date: 2026-02-21
Sprint: 4 - Task 4.4
"""

from typing import List, Optional, Tuple
from ..morphology_flags import MorphologyFlags
from .models import SyntaxFeatures
from .mappings import map_i3rab_to_role


class MorphSyntaxBridge:
    """Infer syntax features from morphology.
    
    Uses morphology features (case, number, gender, definiteness)
    and context (surrounding words) to predict I3rab type and syntactic role.
    """
    
    def __init__(self):
        """Initialize the bridge."""
        pass
    
    def infer_i3rab_type(
        self,
        morph: MorphologyFlags,
        position: int,
        total_words: int,
        prev_morph: Optional[MorphologyFlags] = None,
        context: Optional[dict] = None
    ) -> Tuple[str, float]:
        """Infer I3rab type from morphology.
        
        Args:
            morph: Morphology features of current word
            position: Position in sentence (0-indexed)
            total_words: Total words in sentence
            prev_morph: Morphology of previous word (if available)
            context: Additional context info (e.g. previous word token)
            
        Returns:
            Tuple of (i3rab_type_en, confidence)
        """
        # Get previous word text if available
        prev_word_text = context.get('prev_word_text') if context else None
        curr_word_text = context.get('curr_word_text') if context else None
        
        # Rule 1: Definite nominative at sentence start → مبتدأ (mubtada)
        if position == 0 and morph.definiteness and morph.case == "nominative":
            return "mubtada", 0.8
        
        # Rule 2: Indefinite accusative → مفعول به (maf'ul bihi)
        if not morph.definiteness and morph.case == "accusative":
            return "maf'ul_bihi", 0.7
        
        # Rule 3: Genitive after another word → مضاف إليه (mudaf_ilayhi) or after حرف
        if morph.case == "genitive" and prev_morph:
            # If previous was also genitive or definite, likely mudaf ilayhi
            if prev_morph.case == "nominative" or prev_morph.case == "accusative":
                return "mudaf_ilayhi", 0.7
            # Otherwise might be after preposition (harf)
            return "harf", 0.6
        
        # Rule 4: Nominative after first position → خبر (khabar) or فاعل (fa'il)
        if position > 0 and morph.case == "nominative":
            # If previous was nominative, likely khabar
            if prev_morph and prev_morph.case == "nominative":
                return "khabar", 0.6
            # Otherwise might be fa'il
            return "fa'il", 0.6
        
        # Rule 5: Last position with nominative → خبر (khabar)
        if position == total_words - 1 and morph.case == "nominative":
            return "khabar", 0.5
            
        # --- NEW RULES (Week 1 Integration) ---
        
        # Rule 6: Preposition followers -> Majrur
        # Common prepositions: min, ila, an, ala, fi, bi, li, ka
        if prev_word_text in ["من", "إلى", "عن", "على", "في", "ب", "ل", "ك", "حتى", "مذ", "منذ"]:
             return "mudaf_ilayhi", 0.85 # Using mudaf_ilayhi as general Genitive role for now
             
        # Rule 7: Particles (Inna and sisters) -> Ism Inna (Accusative)
        if prev_word_text in ["إن", "أن", "كأن", "لكن", "ليت", "لعل"] and morph.case == "accusative":
            return "ism_inna", 0.85
            
        # Rule 8: Particles (Kana and sisters) -> Ism Kana (Nominative)
        if prev_word_text in ["كان", "صار", "أصبح", "أمسى", "أضحى", "ظل", "بات", "ليس"] and morph.case == "nominative":
            return "ism_kana", 0.85
            
        # Rule 9: Demonstrative Pronouns -> Mubtada (often)
        if curr_word_text in ["هذا", "هذه", "هذان", "هاتان", "هؤلاء", "ذلك", "تلك", "أولئك"]:
            return "mubtada", 0.75
            
        # Rule 10: Relative Pronouns -> Mawsul (Connector)
        if curr_word_text in ["الذي", "التي", "الذين", "اللاتي", "اللواتي", "من", "ما"]:
            return "mawsul", 0.75
            
        # Rule 11: Vocative (Ya ...) -> Munada
        if prev_word_text in ["يا", "أيا", "هيا", "أي"]:
            return "munada", 0.85
            
        # Rule 12: Haal (Condition) - Indefinite Accusative describing state
        # Usually not at start, indefinite, accusative. 
        # Hard to distinguish from Maf'ul Bihi without semantic context, but give it a chance if late in sentence.
        if position > 2 and morph.case == "accusative" and not morph.definiteness:
             return "hal", 0.5 # Lower confidence due to ambiguity
             
        # Rule 13: Tamyiz (Specification) - Indefinite Accusative after numbers or measures
        # (Placeholder for number detection logic)
        
        # Rule 14: Exception (Mustathna) - after Illa
        if prev_word_text == "إلا" and morph.case == "accusative":
            return "mustathna", 0.85
            
        # Rule 15: Conjunction follower (Ma'touf)
        # If previous is Wa/Fa/Thumma and matches case
        if prev_word_text in ["و", "ف", "ثم", "أو", "أم", "لا", "بل", "لكن", "حتى"] and prev_morph:
            if morph.case == prev_morph.case:
                return "matouf", 0.7
        
        # Default: unknown
        return "unknown", 0.0
    
    def predict_syntax(
        self,
        morph: MorphologyFlags,
        position: int,
        total_words: int,
        prev_morph: Optional[MorphologyFlags] = None,
        context: Optional[dict] = None
    ) -> SyntaxFeatures:
        """Predict syntax features from morphology.
        
        Args:
            morph: Morphology features
            position: Position in sentence
            total_words: Total words in sentence
            prev_morph: Previous word's morphology
            context: Context dictionary (e.g. word text)
            
        Returns:
            SyntaxFeatures with predictions
        """
        # Infer I3rab type
        i3rab_type_en, confidence = self.infer_i3rab_type(
            morph, position, total_words, prev_morph, context
        )
        
        # Map to syntactic role
        syntactic_role = map_i3rab_to_role(i3rab_type_en)
        
        # Map to Arabic
        from .mappings import I3RAB_TYPE_EN_TO_AR
        i3rab_type_ar = I3RAB_TYPE_EN_TO_AR.get(i3rab_type_en, "غير معروف")
        
        # Use case from morphology
        case = morph.case if morph.case else "unknown"
        
        return SyntaxFeatures(
            syntactic_role=syntactic_role,
            case=case,
            i3rab_type_ar=i3rab_type_ar,
            i3rab_type_en=i3rab_type_en,
            confidence=confidence,
        )
    
    def predict_sentence(
        self,
        morphologies: List[MorphologyFlags],
        words: Optional[List[str]] = None
    ) -> List[SyntaxFeatures]:
        """Predict syntax for entire sentence.
        
        Args:
            morphologies: List of morphology features for each word
            words: Optional list of word strings for context
            
        Returns:
            List of syntax features (one per word)
        """
        total_words = len(morphologies)
        predictions = []
        
        for i, morph in enumerate(morphologies):
            prev_morph = morphologies[i - 1] if i > 0 else None
            
            context = {}
            if words:
                context['curr_word_text'] = words[i]
                if i > 0:
                    context['prev_word_text'] = words[i-1]
            
            syntax = self.predict_syntax(
                morph=morph,
                position=i,
                total_words=total_words,
                prev_morph=prev_morph,
                context=context
            )
            
            predictions.append(syntax)
        
        return predictions


class SimpleContextAnalyzer:
    """Simple context analyzer for syntax prediction.
    
    Analyzes surrounding words to improve predictions.
    """
    
    @staticmethod
    def is_after_verb(morphologies: List[MorphologyFlags], position: int) -> bool:
        """Check if current position is after a verb.
        
        Note: Currently simplified - would need POS tagging.
        
        Args:
            morphologies: All morphologies
            position: Current position
            
        Returns:
            False (not implemented without POS)
        """
        # TODO: Implement when POS tagging is available
        return False
    
    @staticmethod
    def is_after_preposition(morphologies: List[MorphologyFlags], position: int) -> bool:
        """Check if current position is after a preposition.
        
        Heuristic: Previous word has genitive case (common after prepositions).
        
        Args:
            morphologies: All morphologies
            position: Current position
            
        Returns:
            True if previous word is genitive
        """
        if position == 0:
            return False
        
        prev = morphologies[position - 1]
        return prev.case == "genitive" if prev.case else False
    
    @staticmethod
    def is_sentence_start(position: int) -> bool:
        """Check if at sentence start.
        
        Args:
            position: Current position
            
        Returns:
            True if at start
        """
        return position == 0
    
    @staticmethod
    def is_sentence_end(position: int, total_words: int) -> bool:
        """Check if at sentence end.
        
        Args:
            position: Current position
            total_words: Total words
            
        Returns:
            True if at end
        """
        return position == total_words - 1


# Convenience function
def predict_syntax_from_morphology(
    morphologies: List[MorphologyFlags],
    words: Optional[List[str]] = None
) -> List[SyntaxFeatures]:
    """Predict syntax from morphology (convenience function).
    
    Args:
        morphologies: List of morphology features
        words: Optional list of word strings
        
    Returns:
        List of syntax predictions
    """
    bridge = MorphSyntaxBridge()
    return bridge.predict_sentence(morphologies, words)