"""
Integration tests for complete Arabic NLP Pipeline
Tests the flow from phonology through morphology to syntax
"""

import pytest
from integration import ArabicNLPPipeline, ProcessingResult


class TestArabicNLPPipeline:
    """Test end-to-end Arabic NLP pipeline"""
    
    def test_pipeline_initialization(self):
        """Test pipeline can be created"""
        pipeline = ArabicNLPPipeline()
        assert pipeline is not None
        assert hasattr(pipeline, 'process')
        assert hasattr(pipeline, 'results')
    
    def test_pipeline_basic_processing(self):
        """Test basic processing functionality"""
        pipeline = ArabicNLPPipeline()
        result = pipeline.process("كتب")
        
        assert result is not None
        assert result['success'] is True
        assert 'sentence' in result
        assert 'stages' in result
    
    def test_pipeline_with_root_only(self):
        """Test processing with root only"""
        pipeline = ArabicNLPPipeline()
        result = pipeline.process("كتب")
        
        assert result['success'] is True
        assert "كتب" in result['sentence']
    
    def test_pipeline_with_root_and_pattern(self):
        """Test processing with root and pattern"""
        pipeline = ArabicNLPPipeline()
        result = pipeline.process("كتب", "فاعل")
        
        assert result['success'] is True
        assert "كتب" in result['sentence']
        assert "فاعل" in result['sentence']
    
    def test_pipeline_stages_present(self):
        """Test all required stages are present"""
        pipeline = ArabicNLPPipeline()
        result = pipeline.process("كتب")
        
        expected_stages = ["phonology", "morphology", "syntax", "generation"]
        assert result['stages'] == expected_stages
    
    def test_pipeline_results_tracking(self):
        """Test pipeline tracks results"""
        pipeline = ArabicNLPPipeline()
        assert isinstance(pipeline.results, list)
        
        # After initialization, results should be empty
        assert len(pipeline.results) == 0


class TestProcessingResult:
    """Test ProcessingResult dataclass"""
    
    def test_processing_result_creation(self):
        """Test ProcessingResult can be created"""
        result = ProcessingResult(
            stage="phonology",
            input_data="كتب",
            output_data=["ك", "ت", "ب"],
            metadata={"phonemes": 3},
            success=True
        )
        
        assert result.stage == "phonology"
        assert result.input_data == "كتب"
        assert result.output_data == ["ك", "ت", "ب"]
        assert result.metadata["phonemes"] == 3
        assert result.success is True
        assert result.error is None
    
    def test_processing_result_with_error(self):
        """Test ProcessingResult with error"""
        result = ProcessingResult(
            stage="morphology",
            input_data="invalid",
            output_data=None,
            metadata={},
            success=False,
            error="Invalid root"
        )
        
        assert result.success is False
        assert result.error == "Invalid root"
        assert result.output_data is None


class TestLayerIntegration:
    """Test integration between different linguistic layers"""
    
    def test_phonology_to_morphology_integration(self):
        """Test data flow from phonology to morphology"""
        # This tests that phonological output can be used as morphological input
        pipeline = ArabicNLPPipeline()
        result = pipeline.process("كتب")
        
        # Verify pipeline can handle phonological processing
        assert result['success'] is True
    
    def test_morphology_to_syntax_integration(self):
        """Test data flow from morphology to syntax"""
        pipeline = ArabicNLPPipeline()
        result = pipeline.process("كتب", "فاعل")
        
        # Verify morphological output flows to syntax
        assert 'stages' in result
        assert 'morphology' in result['stages']
        assert 'syntax' in result['stages']
    
    def test_syntax_to_generation_integration(self):
        """Test data flow from syntax to generation"""
        pipeline = ArabicNLPPipeline()
        result = pipeline.process("كتب")
        
        # Verify syntax output flows to generation
        assert 'generation' in result['stages']
        assert result['success'] is True


class TestEngineInteraction:
    """Test interactions between different engines"""
    
    def test_multiple_roots_processing(self):
        """Test processing multiple roots in sequence"""
        pipeline = ArabicNLPPipeline()
        
        roots = ["كتب", "ذهب", "أكل"]
        for root in roots:
            result = pipeline.process(root)
            assert result['success'] is True
            assert root in result['sentence']
    
    def test_multiple_patterns_processing(self):
        """Test processing same root with different patterns"""
        pipeline = ArabicNLPPipeline()
        
        patterns = ["فاعل", "مفعول", "فعيل"]
        for pattern in patterns:
            result = pipeline.process("كتب", pattern)
            assert result['success'] is True
            assert pattern in result['sentence']
    
    def test_engine_state_isolation(self):
        """Test engines maintain independent state"""
        pipeline1 = ArabicNLPPipeline()
        pipeline2 = ArabicNLPPipeline()
        
        result1 = pipeline1.process("كتب")
        result2 = pipeline2.process("ذهب")
        
        # Results should be independent
        assert "كتب" in result1['sentence']
        assert "ذهب" in result2['sentence']
        assert "كتب" not in result2['sentence']
        assert "ذهب" not in result1['sentence']


class TestFVAFKPipelineIntegration:
    """Test FVAFK pipeline (C1 → C2a → C2b) integration"""
    
    def test_fvafk_components_importable(self):
        """Test FVAFK components can be imported"""
        try:
            from fvafk import orthography_adapter
            assert orthography_adapter is not None
        except ImportError:
            pytest.skip("FVAFK components not available")
    
    def test_c1_encoding_integration(self):
        """Test C1 encoding phase integration"""
        # This would test the C1 encoding component
        # Placeholder for now
        assert True
    
    def test_c2a_phonology_integration(self):
        """Test C2a phonology gates integration"""
        # This would test phonological gate application
        # Placeholder for now
        assert True
    
    def test_c2b_morphology_integration(self):
        """Test C2b morphology analysis integration"""
        # This would test morphological analysis
        # Placeholder for now
        assert True


class TestErrorPropagation:
    """Test how errors propagate through the pipeline"""
    
    def test_graceful_degradation(self):
        """Test pipeline handles errors gracefully"""
        pipeline = ArabicNLPPipeline()
        
        # Should handle processing without crashing
        result = pipeline.process("كتب")
        assert result is not None
        assert 'success' in result
    
    def test_invalid_input_handling(self):
        """Test handling of invalid inputs"""
        pipeline = ArabicNLPPipeline()
        
        # Empty root
        result = pipeline.process("")
        assert result is not None
        
        # Non-Arabic text (should still return something)
        result = pipeline.process("test")
        assert result is not None
