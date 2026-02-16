from dataclasses import dataclass, field
from typing import List, Dict

@dataclass
class WordBoundary:
    word: str
    is_boundary: bool

class CliticDatabase:
    def __init__(self):
        self.prefixes = ["أ", "ال", "ف", "و", "ت", "س"]
        self.suffixes = ["ـه", "ـها", "ـتي", "ـات", "ـي", "ـكم"]

    def is_clitic(self, fragment: str) -> bool:
        return fragment in self.prefixes or fragment in self.suffixes

class WordBoundaryDetectorPlanB:
    def __init__(self, clitic_db: CliticDatabase):
        self.clitic_db = clitic_db

    def detect_boundaries(self, text: str) -> List[WordBoundary]:
        words = text.split()
        boundaries = []
        for word in words:
            boundary = self.is_boundary(word)
            boundaries.append(WordBoundary(word=word, is_boundary=boundary))
        return boundaries

    def is_boundary(self, word: str) -> bool:
        if self.clitic_db.is_clitic(word):
            return False
        return True  # Simplified rule for demonstration

    def confidence_score(self, word: str) -> float:
        # A placeholder for calculating a confidence score
        return 1.0 if self.is_boundary(word) else 0.0

    def convenience_function(self, text: str) -> Dict[str, float]:
        results = self.detect_boundaries(text)
        return {wb.word: self.confidence_score(wb.word) for wb in results}

# Usage Example (This is just a comment in the code)
# clitic_db = CliticDatabase()
# detector = WordBoundaryDetectorPlanB(clitic_db)
# print(detector.convenience_function("أطاب"))