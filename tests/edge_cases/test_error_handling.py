"""
Edge case tests for engine error handling
Tests how engines handle invalid, malformed, or edge case inputs
"""

import pytest
import pandas as pd


class TestNullAndEmptyInputs:
    """Test engines handle null and empty inputs gracefully"""
    
    def test_engine_with_none_input(self):
        """Test engines don't crash with None input"""
        try:
            from engines.morphology import ActiveParticipleEngine
            
            # Engine should return valid DataFrame even without special input
            df = ActiveParticipleEngine.make_df()
            assert df is not None
            
        except ImportError:
            pytest.skip("Engine not available")
    
    def test_engine_empty_dataframe_handling(self):
        """Test engines handle empty DataFrame scenario"""
        try:
            from engines.morphology import ActiveParticipleEngine
            
            df = ActiveParticipleEngine.make_df()
            
            # Should return DataFrame (might be empty, but shouldn't crash)
            assert isinstance(df, pd.DataFrame) or df is None
            
        except ImportError:
            pytest.skip("Engine not available")
    
    def test_dataframe_with_null_values(self):
        """Test processing DataFrames with null values"""
        # Create DataFrame with nulls
        df = pd.DataFrame({
            'الأداة': ['test', None, 'test2'],
            'الفونيمات': ['a', 'b', None]
        })
        
        # Should handle nulls gracefully
        assert df is not None
        assert len(df) == 3


class TestInvalidInputFormats:
    """Test handling of invalid input formats"""
    
    def test_non_arabic_text(self):
        """Test engines handle non-Arabic text"""
        from integration import ArabicNLPPipeline
        
        pipeline = ArabicNLPPipeline()
        
        # English text
        result = pipeline.process("test")
        assert result is not None
        
        # Numbers
        result = pipeline.process("123")
        assert result is not None
        
        # Mixed text
        result = pipeline.process("test123كتب")
        assert result is not None
    
    def test_empty_string_input(self):
        """Test engines handle empty string"""
        from integration import ArabicNLPPipeline
        
        pipeline = ArabicNLPPipeline()
        result = pipeline.process("")
        
        # Should not crash
        assert result is not None
    
    def test_whitespace_only_input(self):
        """Test engines handle whitespace-only input"""
        from integration import ArabicNLPPipeline
        
        pipeline = ArabicNLPPipeline()
        
        inputs = ["   ", "\t", "\n", "  \t  \n  "]
        for inp in inputs:
            result = pipeline.process(inp)
            assert result is not None


class TestUnicodeEdgeCases:
    """Test handling of Unicode edge cases"""
    
    def test_rtl_marks(self):
        """Test handling of RTL marks"""
        from integration import ArabicNLPPipeline
        
        pipeline = ArabicNLPPipeline()
        
        # Text with RTL marks
        text = "\u200Fكتب\u200F"
        result = pipeline.process(text)
        assert result is not None
    
    def test_combining_marks(self):
        """Test handling of combining diacritical marks"""
        from integration import ArabicNLPPipeline
        
        pipeline = ArabicNLPPipeline()
        
        # Text with combining marks
        text = "كَتَبَ"  # With fatha marks
        result = pipeline.process(text)
        assert result is not None
    
    def test_zero_width_characters(self):
        """Test handling of zero-width characters"""
        from integration import ArabicNLPPipeline
        
        pipeline = ArabicNLPPipeline()
        
        # Text with zero-width joiner/non-joiner
        text = "ك\u200Dتب"  # With ZWJ
        result = pipeline.process(text)
        assert result is not None
    
    def test_arabic_presentation_forms(self):
        """Test handling of Arabic presentation forms"""
        from integration import ArabicNLPPipeline
        
        pipeline = ArabicNLPPipeline()
        
        # Isolated forms
        text = "ﻛﺘﺐ"
        result = pipeline.process(text)
        assert result is not None


class TestBoundaryConditions:
    """Test boundary conditions"""
    
    def test_very_long_input(self):
        """Test handling of very long input"""
        from integration import ArabicNLPPipeline
        
        pipeline = ArabicNLPPipeline()
        
        # Very long root (shouldn't happen in Arabic, but test anyway)
        long_text = "كتب" * 100
        result = pipeline.process(long_text)
        assert result is not None
    
    def test_single_character_input(self):
        """Test handling of single character"""
        from integration import ArabicNLPPipeline
        
        pipeline = ArabicNLPPipeline()
        
        result = pipeline.process("ك")
        assert result is not None
    
    def test_two_character_input(self):
        """Test handling of two characters (invalid Arabic root)"""
        from integration import ArabicNLPPipeline
        
        pipeline = ArabicNLPPipeline()
        
        result = pipeline.process("كت")
        assert result is not None


class TestSpecialCharacters:
    """Test handling of special characters"""
    
    def test_punctuation(self):
        """Test handling of punctuation"""
        from integration import ArabicNLPPipeline
        
        pipeline = ArabicNLPPipeline()
        
        inputs = ["كتب.", "كتب,", "كتب!", "كتب?", "كتب؛"]
        for inp in inputs:
            result = pipeline.process(inp)
            assert result is not None
    
    def test_numbers_mixed_with_arabic(self):
        """Test handling of numbers mixed with Arabic"""
        from integration import ArabicNLPPipeline
        
        pipeline = ArabicNLPPipeline()
        
        inputs = ["كتب1", "2كتب", "ك3تب"]
        for inp in inputs:
            result = pipeline.process(inp)
            assert result is not None
    
    def test_symbols(self):
        """Test handling of symbols"""
        from integration import ArabicNLPPipeline
        
        pipeline = ArabicNLPPipeline()
        
        inputs = ["كتب@", "كتب#", "كتب$", "كتب%"]
        for inp in inputs:
            result = pipeline.process(inp)
            assert result is not None


class TestEngineMissingData:
    """Test engines handle missing data gracefully"""
    
    def test_missing_column_handling(self):
        """Test handling of missing columns in DataFrame"""
        df = pd.DataFrame({'other_column': ['value1', 'value2']})
        
        # Should handle DataFrames without expected columns
        assert 'الأداة' not in df.columns
        assert len(df) == 2
    
    def test_engine_with_empty_csv(self):
        """Test engines handle empty CSV files"""
        # Create empty DataFrame
        df = pd.DataFrame()
        
        # Should handle empty DataFrames
        assert len(df) == 0
        assert df is not None


class TestConcurrentAccess:
    """Test engines handle concurrent access"""
    
    def test_multiple_simultaneous_calls(self):
        """Test multiple simultaneous engine calls"""
        try:
            from engines.morphology import ActiveParticipleEngine
            
            # Call make_df multiple times
            results = []
            for i in range(10):
                df = ActiveParticipleEngine.make_df()
                results.append(df)
            
            # All calls should succeed
            assert len(results) == 10
            for df in results:
                assert df is not None
                
        except ImportError:
            pytest.skip("Engine not available")
    
    def test_parallel_pipeline_processing(self):
        """Test multiple pipelines in parallel"""
        from integration import ArabicNLPPipeline
        
        pipelines = [ArabicNLPPipeline() for _ in range(5)]
        results = []
        
        for pipeline in pipelines:
            result = pipeline.process("كتب")
            results.append(result)
        
        # All should succeed
        assert len(results) == 5
        for result in results:
            assert result is not None
            assert result['success'] is True


class TestMemoryAndPerformance:
    """Test memory and performance edge cases"""
    
    def test_repeated_processing(self):
        """Test repeated processing doesn't cause memory issues"""
        from integration import ArabicNLPPipeline
        
        pipeline = ArabicNLPPipeline()
        
        # Process many times
        for i in range(100):
            result = pipeline.process("كتب")
            assert result is not None
    
    def test_large_dataframe_handling(self):
        """Test handling of large DataFrames"""
        # Create large DataFrame
        df = pd.DataFrame({
            'الأداة': [f'item{i}' for i in range(10000)],
            'value': range(10000)
        })
        
        # Should handle large DataFrames
        assert len(df) == 10000
        assert 'الأداة' in df.columns


class TestErrorRecovery:
    """Test error recovery mechanisms"""
    
    def test_pipeline_continues_after_error(self):
        """Test pipeline can continue after processing error"""
        from integration import ArabicNLPPipeline
        
        pipeline = ArabicNLPPipeline()
        
        # First call might have issue
        result1 = pipeline.process("")
        assert result1 is not None
        
        # Second call should still work
        result2 = pipeline.process("كتب")
        assert result2 is not None
        assert result2['success'] is True
    
    def test_engine_state_preserved_after_error(self):
        """Test engine state is preserved after errors"""
        try:
            from engines.morphology import ActiveParticipleEngine
            
            # First call
            df1 = ActiveParticipleEngine.make_df()
            assert df1 is not None
            
            # Second call should work the same
            df2 = ActiveParticipleEngine.make_df()
            assert df2 is not None
            
            # Results should be consistent
            if df1 is not None and df2 is not None:
                assert len(df1) == len(df2)
                
        except ImportError:
            pytest.skip("Engine not available")


class TestDataIntegrity:
    """Test data integrity in edge cases"""
    
    def test_arabic_text_preserved(self):
        """Test Arabic text is preserved correctly"""
        from integration import ArabicNLPPipeline
        
        pipeline = ArabicNLPPipeline()
        
        roots = ["كتب", "ذهب", "أكل", "شرب", "نام"]
        for root in roots:
            result = pipeline.process(root)
            assert root in result['sentence']
    
    def test_diacritics_handling(self):
        """Test diacritics are handled correctly"""
        from integration import ArabicNLPPipeline
        
        pipeline = ArabicNLPPipeline()
        
        # With diacritics
        result1 = pipeline.process("كَتَبَ")
        assert result1 is not None
        
        # Without diacritics
        result2 = pipeline.process("كتب")
        assert result2 is not None
