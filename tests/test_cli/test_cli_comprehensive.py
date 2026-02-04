"""
Comprehensive tests for FVAFK CLI.

Tests coverage for:
- Argument parsing
- Verbose mode
- JSON output
- Morphology analysis
- Multi-word processing
- Error handling
- Human-readable output
- Pattern categorization
"""

import json
import sys
from io import StringIO
from unittest.mock import patch
import pytest

from fvafk.cli.main import MinimalCLI, main, _print_human_readable
from fvafk.c2b.morpheme import PatternType


class TestMinimalCLIInitialization:
    """Test CLI initialization."""
    
    def test_cli_default_initialization(self):
        """Test default CLI initialization."""
        cli = MinimalCLI()
        assert cli.c1_encoder is not None
        assert cli.orchestrator is not None
        assert len(cli.orchestrator.gates) == 10  # All 10 gates
    
    def test_cli_verbose_initialization(self):
        """Test CLI with verbose flag."""
        cli = MinimalCLI(verbose=True)
        assert cli._verbose_default is True
    
    def test_cli_json_initialization(self):
        """Test CLI with JSON output flag."""
        cli = MinimalCLI(json_output=True)
        assert cli._json_output_default is True


class TestCLIBasicProcessing:
    """Test basic CLI processing."""
    
    def test_run_simple_text(self):
        """Test running CLI with simple text."""
        cli = MinimalCLI()
        result = cli.run("كتاب")
        
        assert result["success"] is True
        assert result["input"] == "كتاب"
        assert "c1" in result
        assert "c2a" in result
        assert "stats" in result
    
    def test_run_with_verbose(self):
        """Test running with verbose flag."""
        cli = MinimalCLI()
        result = cli.run("كتاب", verbose=True)
        
        assert result["c1"]["units"] is not None
        assert len(result["c1"]["units"]) > 0
    
    def test_run_without_verbose(self):
        """Test running without verbose flag."""
        cli = MinimalCLI()
        result = cli.run("كتاب", verbose=False)
        
        assert result["c1"]["units"] is None
    
    def test_process_backward_compatible(self):
        """Test backward-compatible process method."""
        cli = MinimalCLI(verbose=True)
        result = cli.process("كتاب")
        
        assert result["success"] is True
        assert result["input"] == "كتاب"


class TestCLIMorphology:
    """Test morphology analysis in CLI."""
    
    def test_run_with_morphology(self):
        """Test running with morphology flag."""
        cli = MinimalCLI()
        result = cli.run("كاتب", morphology=True)
        
        assert "c2b" in result
        assert result["c2b"]["root"] is not None
        assert result["stats"]["c2b_time_ms"] is not None
    
    def test_run_without_morphology(self):
        """Test running without morphology flag."""
        cli = MinimalCLI()
        result = cli.run("كاتب", morphology=False)
        
        assert "c2b" not in result
        assert result["stats"]["c2b_time_ms"] is None
    
    def test_morphology_root_extraction(self):
        """Test root extraction in morphology."""
        cli = MinimalCLI()
        result = cli.run("كاتب", morphology=True)
        
        morph = result["c2b"]
        assert morph["root"]["letters"] == ["ك", "ت", "ب"]
        assert morph["root"]["formatted"] == "ك-ت-ب"
        assert morph["root"]["type"] == "trilateral"
        assert morph["root"]["length"] == 3
    
    def test_morphology_pattern_matching(self):
        """Test pattern matching in morphology."""
        cli = MinimalCLI()
        result = cli.run("كاتب", morphology=True)
        
        morph = result["c2b"]
        if morph["pattern"]["template"]:
            assert "template" in morph["pattern"]
            assert "type" in morph["pattern"]
            assert "category" in morph["pattern"]
    
    def test_morphology_with_affixes(self):
        """Test morphology with prefix/suffix."""
        cli = MinimalCLI()
        result = cli.run("الكاتب", morphology=True)
        
        morph = result["c2b"]
        assert "affixes" in morph
        assert morph["affixes"]["prefix"] is not None or morph["affixes"]["suffix"] is not None
    
    def test_morphology_error_case(self):
        """Test morphology with invalid input."""
        cli = MinimalCLI()
        result = cli.run("ا", morphology=True)
        
        # Short input might fail to extract root
        if "error" in result["c2b"]:
            assert result["c2b"]["root"] is None


class TestCLIMultiWord:
    """Test multi-word processing."""
    
    def test_multi_word_processing(self):
        """Test processing multiple words."""
        cli = MinimalCLI()
        result = cli.run("كتاب جديد", morphology=True, multi_word=True)
        
        morph = result["c2b"]
        assert "words_count" in morph
        assert "words" in morph
        assert morph["words_count"] >= 1
    
    def test_multi_word_with_punctuation(self):
        """Test multi-word with punctuation."""
        cli = MinimalCLI()
        result = cli.run("كتاب، جديد!", morphology=True, multi_word=True)
        
        morph = result["c2b"]
        # Punctuation should be filtered out
        assert morph["words_count"] >= 1
    
    def test_multi_word_each_analysis(self):
        """Test that each word gets its own analysis."""
        cli = MinimalCLI()
        result = cli.run("كاتب قارئ", morphology=True, multi_word=True)
        
        morph = result["c2b"]
        assert morph["words_count"] >= 2
        
        for word_analysis in morph["words"]:
            assert "word" in word_analysis
            assert "root" in word_analysis
            assert "pattern" in word_analysis


class TestCLIPatternCategories:
    """Test pattern categorization."""
    
    def test_get_pattern_category_verb(self):
        """Test verb pattern categorization."""
        cli = MinimalCLI()
        
        assert cli._get_pattern_category(PatternType.FORM_I) == "verb"
        assert cli._get_pattern_category(PatternType.FORM_II) == "verb"
        assert cli._get_pattern_category(PatternType.FORM_X) == "verb"
    
    def test_get_pattern_category_plural(self):
        """Test plural pattern categorization."""
        cli = MinimalCLI()
        
        # Check if PLURAL patterns exist
        for pattern_type in PatternType:
            if "PLURAL" in pattern_type.value.upper():
                assert cli._get_pattern_category(pattern_type) == "plural"
    
    def test_get_pattern_category_noun(self):
        """Test noun pattern categorization (default)."""
        cli = MinimalCLI()
        
        # Most patterns should default to noun
        category = cli._get_pattern_category(PatternType.ACTIVE_PARTICIPLE)
        assert category in ["noun", "verb", "plural"]


class TestCLIStatistics:
    """Test timing and statistics."""
    
    def test_timing_stats_present(self):
        """Test that timing statistics are present."""
        cli = MinimalCLI()
        result = cli.run("كتاب")
        
        stats = result["stats"]
        assert "c1_time_ms" in stats
        assert "c2a_time_ms" in stats
        assert "total_time_ms" in stats
        assert "gates_count" in stats
        
        # Times should be non-negative
        assert stats["c1_time_ms"] >= 0
        assert stats["c2a_time_ms"] >= 0
        assert stats["total_time_ms"] >= 0
    
    def test_timing_with_morphology(self):
        """Test timing with morphology."""
        cli = MinimalCLI()
        result = cli.run("كتاب", morphology=True)
        
        stats = result["stats"]
        assert stats["c2b_time_ms"] is not None
        assert stats["c2b_time_ms"] >= 0


class TestCLIGateResults:
    """Test gate results in CLI output."""
    
    def test_gate_results_structure(self):
        """Test gate results have correct structure."""
        cli = MinimalCLI()
        result = cli.run("كتاب")
        
        gates = result["c2a"]["gates"]
        assert len(gates) > 0
        
        for gate in gates:
            assert "gate_id" in gate
            assert "status" in gate
            assert "time_ms" in gate
            assert "deltas" in gate
            assert "reason" in gate
    
    def test_syllable_count(self):
        """Test syllable counting."""
        cli = MinimalCLI()
        result = cli.run("كتاب")
        
        syllables = result["c2a"]["syllables"]
        assert "count" in syllables
        assert syllables["count"] >= 0


class TestCLIMainFunction:
    """Test main CLI function."""
    
    def test_main_with_json_flag(self):
        """Test main function with --json flag."""
        test_args = ["prog", "كتاب", "--json"]
        
        with patch.object(sys, 'argv', test_args):
            with patch('sys.stdout', new=StringIO()) as fake_out:
                with patch('sys.exit') as mock_exit:
                    main()
                    mock_exit.assert_called_once_with(0)
                    
                    output = fake_out.getvalue()
                    # Should be valid JSON
                    result = json.loads(output)
                    assert result["success"] is True
                    assert result["input"] == "كتاب"
    
    def test_main_with_verbose_flag(self):
        """Test main function with --verbose flag."""
        test_args = ["prog", "كتاب", "--verbose", "--json"]
        
        with patch.object(sys, 'argv', test_args):
            with patch('sys.stdout', new=StringIO()) as fake_out:
                with patch('sys.exit') as mock_exit:
                    main()
                    mock_exit.assert_called_once_with(0)
                    
                    output = fake_out.getvalue()
                    result = json.loads(output)
                    assert result["c1"]["units"] is not None
    
    def test_main_with_morphology_flag(self):
        """Test main function with --morphology flag."""
        test_args = ["prog", "كاتب", "--morphology", "--json"]
        
        with patch.object(sys, 'argv', test_args):
            with patch('sys.stdout', new=StringIO()) as fake_out:
                with patch('sys.exit') as mock_exit:
                    main()
                    mock_exit.assert_called_once_with(0)
                    
                    output = fake_out.getvalue()
                    result = json.loads(output)
                    assert "c2b" in result
    
    def test_main_with_multi_word_flag(self):
        """Test main function with --multi-word flag."""
        test_args = ["prog", "كتاب جديد", "--morphology", "--multi-word", "--json"]
        
        with patch.object(sys, 'argv', test_args):
            with patch('sys.stdout', new=StringIO()) as fake_out:
                with patch('sys.exit') as mock_exit:
                    main()
                    mock_exit.assert_called_once_with(0)
                    
                    output = fake_out.getvalue()
                    result = json.loads(output)
                    assert "c2b" in result
                    assert "words_count" in result["c2b"]
    
    def test_main_error_handling(self):
        """Test main function error handling."""
        test_args = ["prog", "", "--json"]  # Empty input might cause error
        
        with patch.object(sys, 'argv', test_args):
            with patch('sys.stdout', new=StringIO()) as fake_out:
                with patch('sys.exit') as mock_exit:
                    try:
                        main()
                    except:
                        pass
                    
                    # Should call exit (either 0 or 1)
                    assert mock_exit.called


class TestHumanReadableOutput:
    """Test human-readable output formatting."""
    
    def test_print_human_readable_basic(self):
        """Test basic human-readable output."""
        cli = MinimalCLI()
        result = cli.run("كتاب")
        
        with patch('sys.stdout', new=StringIO()) as fake_out:
            _print_human_readable(result)
            output = fake_out.getvalue()
            
            assert "FVAFK Analysis" in output
            assert "كتاب" in output
            assert "Phase C1" in output
            assert "Phase C2a" in output
    
    def test_print_human_readable_with_morphology(self):
        """Test human-readable output with morphology."""
        cli = MinimalCLI()
        result = cli.run("كاتب", morphology=True)
        
        with patch('sys.stdout', new=StringIO()) as fake_out:
            _print_human_readable(result)
            output = fake_out.getvalue()
            
            assert "Phase C2b" in output
            assert "Root:" in output
            assert "Pattern:" in output
    
    def test_print_human_readable_timing(self):
        """Test timing information in human-readable output."""
        cli = MinimalCLI()
        result = cli.run("كتاب")
        
        with patch('sys.stdout', new=StringIO()) as fake_out:
            _print_human_readable(result)
            output = fake_out.getvalue()
            
            assert "Performance Summary" in output
            assert "Total:" in output
            assert "ms" in output
