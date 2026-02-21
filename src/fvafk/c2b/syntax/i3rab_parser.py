"""I3rab Parser - Extract structured data from Arabic I3rab text.

This parser uses regex patterns to extract I3rab components from
the raw Arabic I3rab descriptions in the corpus.

Author: Hussein Hiyassat
Date: 2026-02-21
Sprint: 4 - Task 4.2
"""

import re
from typing import Optional, Tuple
from .models import I3rabComponents
from .mappings import CASE_AR_TO_EN, I3RAB_TYPE_AR_TO_EN, CASE_MARKER_AR_TO_EN


class I3rabParser:
    """Parse I3rab text using regex patterns.
    
    Extracts:
    - I3rab type (مبتدأ، خبر، فاعل، مفعول به، حرف)
    - Case (مرفوع، منصوب، مجرور)
    - Case marker (الضمة، الفتحة، الكسرة)
    - Mahall (في محل / لا محل له من الإعراب)
    """
    
    # Regex patterns for extraction
    PATTERNS = {
        # I3rab types (Top 5 priority)
        "i3rab_type": r"(مبتدأ|خبر|فاعل|مفعول به|حرف جر|حرف)",
        
        # Case markers
        "case": r"(مرفوع|منصوب|مجرور|مبني)",
        
        # Case marker signs
        "case_marker": r"(الضمة|الفتحة|الكسرة|الواو|الياء|الألف)",
        
        # Mahall (syntactic position)
        "mahall": r"(في محل|لا محل له)",
    }
    
    def __init__(self):
        """Initialize parser with compiled regex patterns."""
        self.compiled_patterns = {
            key: re.compile(pattern)
            for key, pattern in self.PATTERNS.items()
        }
    
    def parse(self, i3rab_text: str) -> I3rabComponents:
        """Parse I3rab text and extract components.
        
        Args:
            i3rab_text: Raw Arabic I3rab description
            
        Returns:
            I3rabComponents with extracted data
        """
        components = I3rabComponents(raw_text=i3rab_text)
        
        # Extract I3rab type
        i3rab_type_ar = self._extract_pattern(i3rab_text, "i3rab_type")
        if i3rab_type_ar:
            # Handle "حرف جر" → "حرف"
            i3rab_type_ar = i3rab_type_ar.replace("حرف جر", "حرف")
            components.i3rab_type = I3RAB_TYPE_AR_TO_EN.get(i3rab_type_ar)
        
        # Extract case
        case_ar = self._extract_pattern(i3rab_text, "case")
        if case_ar and case_ar != "مبني":  # Skip mabni (indeclinable)
            components.case = CASE_AR_TO_EN.get(case_ar)
        
        # Extract case marker
        marker_ar = self._extract_pattern(i3rab_text, "case_marker")
        if marker_ar:
            components.case_marker = CASE_MARKER_AR_TO_EN.get(marker_ar)
        
        # Extract mahall
        mahall = self._extract_pattern(i3rab_text, "mahall")
        if mahall:
            components.mahall = mahall
        
        # Compute confidence
        components.confidence = self._compute_confidence(components)
        
        return components
    
    def _extract_pattern(self, text: str, pattern_name: str) -> Optional[str]:
        """Extract first match for a pattern.
        
        Args:
            text: Text to search
            pattern_name: Name of pattern to use
            
        Returns:
            First matched group or None
        """
        pattern = self.compiled_patterns.get(pattern_name)
        if not pattern:
            return None
        
        match = pattern.search(text)
        return match.group(1) if match else None
    
    def _compute_confidence(self, components: I3rabComponents) -> float:
        """Compute parsing confidence based on extracted components.
        
        Confidence factors:
        - Has I3rab type: +0.4
        - Has case: +0.3
        - Has case marker: +0.2
        - Has mahall: +0.1
        
        Args:
            components: Parsed components
            
        Returns:
            Confidence score 0.0-1.0
        """
        confidence = 0.0
        
        if components.i3rab_type:
            confidence += 0.4
        
        if components.case:
            confidence += 0.3
        
        if components.case_marker:
            confidence += 0.2
        
        if components.mahall:
            confidence += 0.1
        
        return min(confidence, 1.0)  # Cap at 1.0
    
    def parse_with_validation(self, i3rab_text: str) -> Tuple[I3rabComponents, bool]:
        """Parse and validate I3rab text.
        
        Args:
            i3rab_text: Raw Arabic I3rab description
            
        Returns:
            Tuple of (components, is_valid)
            is_valid is True if at least I3rab type was extracted
        """
        components = self.parse(i3rab_text)
        is_valid = components.i3rab_type is not None
        return components, is_valid


# Convenience function
def parse_i3rab(i3rab_text: str) -> I3rabComponents:
    """Parse I3rab text (convenience function).
    
    Args:
        i3rab_text: Raw Arabic I3rab description
        
    Returns:
        Parsed I3rabComponents
    """
    parser = I3rabParser()
    return parser.parse(i3rab_text)