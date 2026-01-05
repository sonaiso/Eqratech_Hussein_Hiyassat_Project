"""
Speech Act Layer

Implements the six fundamental Arabic speech act types:
1. KHABAR (خبر): Declarative - informing
2. TALAB (طلب): Imperative - requesting/commanding
3. ISTIFHAM (استفهام): Interrogative - questioning
4. TA3AJJUB (تعجب): Exclamatory - expressing wonder
5. TAMANNI (تمنّي): Optative - expressing wish (low feasibility)
6. TARAJJI (ترجّي): Hopeful - expressing hope (probable)

Each type has subtypes that refine the classification.
"""

from enum import Enum
from dataclasses import dataclass
from typing import List, Optional, Dict, Any


class SpeechActType(Enum):
    """Main speech act types"""
    KHABAR = "KHABAR"          # خبر - Declarative
    TALAB = "TALAB"            # طلب - Imperative
    ISTIFHAM = "ISTIFHAM"      # استفهام - Interrogative
    TA3AJJUB = "TA3AJJUB"      # تعجب - Exclamatory
    TAMANNI = "TAMANNI"        # تمنّي - Optative/Wish
    TARAJJI = "TARAJJI"        # ترجّي - Hopeful


class KhabarSubtype(Enum):
    """Subtypes of KHABAR (خبر)"""
    ITHBAT = "ITHBAT"          # إثبات - Affirmation
    NAFY = "NAFY"              # نفي - Negation
    TAQRIR = "TAQRIR"          # تقرير - Confirmation/Assertion


class TalabSubtype(Enum):
    """Subtypes of TALAB (طلب)"""
    AMR = "AMR"                # أمر - Command
    NAHY = "NAHY"              # نهي - Prohibition
    DUAA = "DUAA"              # دعاء - Supplication
    ARD = "3ARD"               # عرض - Offer
    TAHDID = "TAHDID"          # تحضيض - Urging
    TAHDEED = "TAHDEED"        # تهديد - Warning/Threat
    ILTIMAS = "ILTIMAS"        # التماس - Request (polite)


class IstifhamSubtype(Enum):
    """Subtypes of ISTIFHAM (استفهام)"""
    TASAWUR = "TASAWUR"        # تصور - Conceptual question (which/what)
    TASDIQ = "TASDIQ"          # تصديق - Yes/no question


class Ta3ajjubSubtype(Enum):
    """Subtypes of TA3AJJUB (تعجب)"""
    EVAL_AROUSAL = "EVAL_AROUSAL"  # تعجب تقييمي - Evaluative exclamation
    FORMULA_MA = "FORMULA_MA"      # صيغة ما أفعل
    FORMULA_AF3IL = "FORMULA_AF3IL" # صيغة أفعل به


class TamanniSubtype(Enum):
    """Subtypes of TAMANNI (تمنّي)"""
    LOW_FEASIBILITY = "LOW_FEASIBILITY"      # منخفض الإمكانية
    IMPOSSIBLE = "IMPOSSIBLE"                 # مستحيل
    DISTANT = "DISTANT"                       # بعيد المنال


class TarajjiSubtype(Enum):
    """Subtypes of TARAJJI (ترجّي)"""
    HIGH_HOPE = "HIGH_HOPE"                  # رجاء قوي
    PROBABLE = "PROBABLE"                    # محتمل
    EXPECTATION = "EXPECTATION"              # توقع


@dataclass
class SpeechAct:
    """
    Complete speech act representation.
    
    Attributes:
        act_type: Main speech act type
        subtype: Specific subtype
        tool_id: Linguistic tool/particle used (e.g., هل، ما، أين)
        confidence: Confidence level (0.0-1.0)
        features: Additional features
    """
    act_type: SpeechActType
    subtype: Optional[str] = None
    tool_id: Optional[str] = None
    confidence: float = 1.0
    features: Dict[str, Any] = None
    
    def __post_init__(self):
        if self.features is None:
            self.features = {}
    
    def to_dict(self) -> dict:
        """Convert to dictionary representation"""
        return {
            'type': self.act_type.value,
            'subtype': self.subtype,
            'tool_id': self.tool_id,
            'confidence': self.confidence,
            'features': self.features
        }


class SpeechActClassifier:
    """
    Classifier for determining speech act types.
    
    Uses linguistic features, particles, and sentence structure
    to classify utterances into speech act types.
    """
    
    # Interrogative particles
    INTERROGATIVE_PARTICLES = {
        'هل': ('TASDIQ', 'yes_no_question'),
        'أ': ('TASDIQ', 'yes_no_question'),
        'ما': ('TASAWUR', 'what'),
        'ماذا': ('TASAWUR', 'what'),
        'من': ('TASAWUR', 'who'),
        'أين': ('TASAWUR', 'where'),
        'متى': ('TASAWUR', 'when'),
        'كيف': ('TASAWUR', 'how'),
        'لماذا': ('TASAWUR', 'why'),
        'كم': ('TASAWUR', 'how_many'),
        'أي': ('TASAWUR', 'which'),
        'أين': ('TASAWUR', 'where'),
    }
    
    # Negation particles
    NEGATION_PARTICLES = ['لا', 'ما', 'لم', 'لن', 'ليس']
    
    # Wish particles
    WISH_PARTICLES = ['ليت', 'لو']
    
    # Hope particles
    HOPE_PARTICLES = ['لعل', 'عسى']
    
    # Exclamation patterns
    EXCLAMATION_PATTERNS = ['ما أفعل', 'أفعل به']
    
    def __init__(self):
        """Initialize classifier"""
        self.rules = self._build_rules()
    
    def _build_rules(self) -> List[callable]:
        """Build classification rules in priority order"""
        return [
            self._check_wish,
            self._check_hope,
            self._check_exclamation,  # Check exclamation before interrogative
            self._check_interrogative,
            self._check_imperative,
            self._check_negation,
            self._check_declarative,
        ]
    
    def classify(self, tokens: List[str], features: Dict[str, Any] = None) -> SpeechAct:
        """
        Classify tokens into speech act.
        
        Args:
            tokens: List of tokens/words
            features: Additional linguistic features
            
        Returns:
            SpeechAct object
        """
        if not tokens:
            return SpeechAct(SpeechActType.KHABAR, KhabarSubtype.ITHBAT.value)
        
        features = features or {}
        
        # Apply rules in order
        for rule in self.rules:
            result = rule(tokens, features)
            if result:
                return result
        
        # Default to KHABAR/ITHBAT
        return SpeechAct(SpeechActType.KHABAR, KhabarSubtype.ITHBAT.value)
    
    def _check_interrogative(self, tokens: List[str], features: Dict) -> Optional[SpeechAct]:
        """Check for interrogative (استفهام)"""
        first_token = tokens[0] if tokens else None
        
        if first_token in self.INTERROGATIVE_PARTICLES:
            subtype, tool = self.INTERROGATIVE_PARTICLES[first_token]
            return SpeechAct(
                act_type=SpeechActType.ISTIFHAM,
                subtype=subtype,
                tool_id=first_token,
                features={'tool_type': tool}
            )
        
        # Check for question mark (in case of punctuation)
        if any(t in ['؟', '?'] for t in tokens):
            return SpeechAct(
                act_type=SpeechActType.ISTIFHAM,
                subtype=IstifhamSubtype.TASDIQ.value
            )
        
        return None
    
    def _check_wish(self, tokens: List[str], features: Dict) -> Optional[SpeechAct]:
        """Check for wish (تمنّي)"""
        first_token = tokens[0] if tokens else None
        
        if first_token in self.WISH_PARTICLES:
            return SpeechAct(
                act_type=SpeechActType.TAMANNI,
                subtype=TamanniSubtype.LOW_FEASIBILITY.value,
                tool_id=first_token
            )
        
        return None
    
    def _check_hope(self, tokens: List[str], features: Dict) -> Optional[SpeechAct]:
        """Check for hope (ترجّي)"""
        first_token = tokens[0] if tokens else None
        
        if first_token in self.HOPE_PARTICLES:
            return SpeechAct(
                act_type=SpeechActType.TARAJJI,
                subtype=TarajjiSubtype.HIGH_HOPE.value,
                tool_id=first_token
            )
        
        return None
    
    def _check_exclamation(self, tokens: List[str], features: Dict) -> Optional[SpeechAct]:
        """Check for exclamation (تعجب)"""
        # Check for exclamation patterns
        text = ' '.join(tokens)
        
        if text.startswith('ما أ') or 'ما أ' in text:
            return SpeechAct(
                act_type=SpeechActType.TA3AJJUB,
                subtype=Ta3ajjubSubtype.FORMULA_MA.value
            )
        
        # Check for exclamation mark
        if any(t in ['!', '！'] for t in tokens):
            return SpeechAct(
                act_type=SpeechActType.TA3AJJUB,
                subtype=Ta3ajjubSubtype.EVAL_AROUSAL.value
            )
        
        return None
    
    def _check_imperative(self, tokens: List[str], features: Dict) -> Optional[SpeechAct]:
        """Check for imperative (طلب)"""
        # Check verb mood from features
        verb_mood = features.get('verb_mood')
        
        if verb_mood == 'imperative':
            return SpeechAct(
                act_type=SpeechActType.TALAB,
                subtype=TalabSubtype.AMR.value
            )
        
        # Check for prohibition (لا + jussive)
        if len(tokens) >= 2 and tokens[0] == 'لا':
            if features.get('verb_mood') == 'jussive':
                return SpeechAct(
                    act_type=SpeechActType.TALAB,
                    subtype=TalabSubtype.NAHY.value,
                    tool_id='لا'
                )
        
        return None
    
    def _check_negation(self, tokens: List[str], features: Dict) -> Optional[SpeechAct]:
        """Check for negation (نفي)"""
        # Check if any negation particle present
        if any(t in self.NEGATION_PARTICLES for t in tokens):
            return SpeechAct(
                act_type=SpeechActType.KHABAR,
                subtype=KhabarSubtype.NAFY.value
            )
        
        return None
    
    def _check_declarative(self, tokens: List[str], features: Dict) -> Optional[SpeechAct]:
        """Default to declarative (خبر إثبات)"""
        return SpeechAct(
            act_type=SpeechActType.KHABAR,
            subtype=KhabarSubtype.ITHBAT.value
        )


def create_speech_act(act_type: str, subtype: str = None, 
                     tool_id: str = None) -> SpeechAct:
    """
    Factory function to create speech act.
    
    Args:
        act_type: Speech act type name
        subtype: Subtype name
        tool_id: Tool/particle ID
        
    Returns:
        SpeechAct object
    """
    act_enum = SpeechActType[act_type]
    return SpeechAct(act_type=act_enum, subtype=subtype, tool_id=tool_id)
