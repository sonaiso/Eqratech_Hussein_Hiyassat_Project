"""
Tests for Phase 2: Speech Act Layer

Tests the 6 speech act types and their subtypes:
- KHABAR (خبر): ITHBAT, NAFY, TAQRIR
- TALAB (طلب): AMR, NAHY, DUAA, etc.
- ISTIFHAM (استفهام): TASAWUR, TASDIQ
- TA3AJJUB (تعجب): EVAL_AROUSAL, FORMULA_MA, FORMULA_AF3IL
- TAMANNI (تمنّي): LOW_FEASIBILITY, IMPOSSIBLE, DISTANT
- TARAJJI (ترجّي): HIGH_HOPE, PROBABLE, EXPECTATION
"""

import pytest
from pathlib import Path
import sys

# Add kernel to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from fractalhub.kernel.speech_acts import (
    SpeechAct, SpeechActType, SpeechActClassifier,
    KhabarSubtype, TalabSubtype, IstifhamSubtype,
    Ta3ajjubSubtype, TamanniSubtype, TarajjiSubtype,
    create_speech_act
)
from fractalhub.kernel.gates import SpeechActGate


class TestSpeechActTypes:
    """Tests for speech act type enumerations"""
    
    def test_speech_act_types_exist(self):
        """Test all 6 main types exist"""
        assert SpeechActType.KHABAR.value == "KHABAR"
        assert SpeechActType.TALAB.value == "TALAB"
        assert SpeechActType.ISTIFHAM.value == "ISTIFHAM"
        assert SpeechActType.TA3AJJUB.value == "TA3AJJUB"
        assert SpeechActType.TAMANNI.value == "TAMANNI"
        assert SpeechActType.TARAJJI.value == "TARAJJI"
    
    def test_khabar_subtypes(self):
        """Test KHABAR subtypes"""
        assert KhabarSubtype.ITHBAT.value == "ITHBAT"
        assert KhabarSubtype.NAFY.value == "NAFY"
        assert KhabarSubtype.TAQRIR.value == "TAQRIR"
    
    def test_talab_subtypes(self):
        """Test TALAB subtypes"""
        assert TalabSubtype.AMR.value == "AMR"
        assert TalabSubtype.NAHY.value == "NAHY"
        assert TalabSubtype.DUAA.value == "DUAA"
    
    def test_istifham_subtypes(self):
        """Test ISTIFHAM subtypes"""
        assert IstifhamSubtype.TASAWUR.value == "TASAWUR"
        assert IstifhamSubtype.TASDIQ.value == "TASDIQ"


class TestSpeechActObject:
    """Tests for SpeechAct dataclass"""
    
    def test_create_speech_act(self):
        """Test creating speech act object"""
        act = SpeechAct(
            act_type=SpeechActType.KHABAR,
            subtype=KhabarSubtype.ITHBAT.value
        )
        
        assert act.act_type == SpeechActType.KHABAR
        assert act.subtype == "ITHBAT"
        assert act.confidence == 1.0
    
    def test_speech_act_with_tool(self):
        """Test speech act with tool_id"""
        act = SpeechAct(
            act_type=SpeechActType.ISTIFHAM,
            subtype=IstifhamSubtype.TASAWUR.value,
            tool_id="هل"
        )
        
        assert act.tool_id == "هل"
    
    def test_speech_act_to_dict(self):
        """Test serialization to dict"""
        act = SpeechAct(
            act_type=SpeechActType.TALAB,
            subtype=TalabSubtype.AMR.value
        )
        
        result = act.to_dict()
        
        assert result['type'] == "TALAB"
        assert result['subtype'] == "AMR"
        assert 'confidence' in result


class TestSpeechActClassifier:
    """Tests for speech act classification"""
    
    def setup_method(self):
        """Setup classifier for each test"""
        self.classifier = SpeechActClassifier()
    
    def test_classify_khabar_ithbat(self):
        """Test classifying affirmative declarative (خبر إثبات)"""
        tokens = ['كتب', 'الطالب', 'الدرس']
        
        result = self.classifier.classify(tokens)
        
        assert result.act_type == SpeechActType.KHABAR
        assert result.subtype == KhabarSubtype.ITHBAT.value
    
    def test_classify_khabar_nafy(self):
        """Test classifying negative declarative (خبر نفي)"""
        tokens = ['لم', 'يكتب', 'الطالب', 'الدرس']
        
        result = self.classifier.classify(tokens)
        
        assert result.act_type == SpeechActType.KHABAR
        assert result.subtype == KhabarSubtype.NAFY.value
    
    def test_classify_istifham_tasdiq(self):
        """Test classifying yes/no question (استفهام تصديق)"""
        tokens = ['هل', 'كتب', 'الطالب', 'الدرس', '؟']
        
        result = self.classifier.classify(tokens)
        
        assert result.act_type == SpeechActType.ISTIFHAM
        assert result.subtype == IstifhamSubtype.TASDIQ.value
        assert result.tool_id == 'هل'
    
    def test_classify_istifham_tasawur(self):
        """Test classifying conceptual question (استفهام تصور)"""
        tokens = ['من', 'كتب', 'الدرس', '؟']
        
        result = self.classifier.classify(tokens)
        
        assert result.act_type == SpeechActType.ISTIFHAM
        assert result.subtype == IstifhamSubtype.TASAWUR.value
        assert result.tool_id == 'من'
    
    def test_classify_tamanni(self):
        """Test classifying wish (تمنّي)"""
        tokens = ['ليت', 'الشباب', 'يعود']
        
        result = self.classifier.classify(tokens)
        
        assert result.act_type == SpeechActType.TAMANNI
        assert result.subtype == TamanniSubtype.LOW_FEASIBILITY.value
        assert result.tool_id == 'ليت'
    
    def test_classify_tarajji(self):
        """Test classifying hope (ترجّي)"""
        tokens = ['لعل', 'الله', 'يرحمنا']
        
        result = self.classifier.classify(tokens)
        
        assert result.act_type == SpeechActType.TARAJJI
        assert result.subtype == TarajjiSubtype.HIGH_HOPE.value
        assert result.tool_id == 'لعل'
    
    def test_classify_ta3ajjub(self):
        """Test classifying exclamation (تعجب)"""
        tokens = ['ما', 'أجمل', 'الطبيعة', '!']
        
        result = self.classifier.classify(tokens)
        
        assert result.act_type == SpeechActType.TA3AJJUB
        # Could be FORMULA_MA or EVAL_AROUSAL
        assert result.act_type == SpeechActType.TA3AJJUB
    
    def test_classify_talab_amr(self):
        """Test classifying command (طلب أمر)"""
        tokens = ['اكتب', 'الدرس']
        features = {'verb_mood': 'imperative'}
        
        result = self.classifier.classify(tokens, features)
        
        assert result.act_type == SpeechActType.TALAB
        assert result.subtype == TalabSubtype.AMR.value
    
    def test_classify_talab_nahy(self):
        """Test classifying prohibition (طلب نهي)"""
        tokens = ['لا', 'تكتب', 'على', 'الحائط']
        features = {'verb_mood': 'jussive'}
        
        result = self.classifier.classify(tokens, features)
        
        assert result.act_type == SpeechActType.TALAB
        assert result.subtype == TalabSubtype.NAHY.value


class TestSpeechActGate:
    """Tests for G_SPEECH_ACT gate"""
    
    def test_gate_basic_classification(self):
        """Test gate classifies correctly"""
        gate = SpeechActGate("G_SPEECH_ACT")
        
        tokens = ['كتب', 'الطالب']
        result = gate.execute([tokens], [])
        
        assert len(result) == 1
        speech_act_dict = result[0]
        
        assert speech_act_dict['type'] == 'KHABAR'
        assert speech_act_dict['subtype'] == 'ITHBAT'
    
    def test_gate_with_interrogative(self):
        """Test gate with interrogative"""
        gate = SpeechActGate("G_SPEECH_ACT")
        
        tokens = ['هل', 'كتبت', 'الدرس']
        result = gate.execute([tokens], [])
        
        speech_act_dict = result[0]
        
        assert speech_act_dict['type'] == 'ISTIFHAM'
        assert speech_act_dict['tool_id'] == 'هل'
    
    def test_gate_with_features(self):
        """Test gate with additional features"""
        gate = SpeechActGate("G_SPEECH_ACT")
        
        tokens = ['اكتب']
        features = {'verb_mood': 'imperative'}
        result = gate.execute([tokens, features], [])
        
        speech_act_dict = result[0]
        
        assert speech_act_dict['type'] == 'TALAB'
        assert speech_act_dict['subtype'] == 'AMR'


class TestFactoryFunction:
    """Tests for create_speech_act factory"""
    
    def test_create_khabar(self):
        """Test factory creates KHABAR"""
        act = create_speech_act('KHABAR', 'ITHBAT')
        
        assert act.act_type == SpeechActType.KHABAR
        assert act.subtype == 'ITHBAT'
    
    def test_create_with_tool(self):
        """Test factory with tool_id"""
        act = create_speech_act('ISTIFHAM', 'TASAWUR', 'من')
        
        assert act.act_type == SpeechActType.ISTIFHAM
        assert act.subtype == 'TASAWUR'
        assert act.tool_id == 'من'


class TestMultipleSentences:
    """Test classification of various Arabic sentences"""
    
    def setup_method(self):
        """Setup classifier"""
        self.classifier = SpeechActClassifier()
    
    def test_various_declaratives(self):
        """Test various declarative sentences"""
        test_cases = [
            (['الشمس', 'مشرقة'], 'ITHBAT'),
            (['لا', 'أحد', 'هنا'], 'NAFY'),
            (['ليس', 'الأمر', 'سهلاً'], 'NAFY'),
        ]
        
        for tokens, expected_subtype in test_cases:
            result = self.classifier.classify(tokens)
            assert result.act_type == SpeechActType.KHABAR
            assert result.subtype == expected_subtype
    
    def test_various_questions(self):
        """Test various question types"""
        test_cases = [
            (['ما', 'اسمك'], 'TASAWUR'),
            (['أين', 'الكتاب'], 'TASAWUR'),
            (['كيف', 'حالك'], 'TASAWUR'),
            (['متى', 'تذهب'], 'TASAWUR'),
        ]
        
        for tokens, expected_subtype in test_cases:
            result = self.classifier.classify(tokens)
            assert result.act_type == SpeechActType.ISTIFHAM
            assert result.subtype == expected_subtype


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
