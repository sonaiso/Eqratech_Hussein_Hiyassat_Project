"""
Tests for CLI syntax output integration.

Verifies that running the CLI with --morphology --json produces
a 'syntax' key in the output with the expected structure.

Author: Hussein Hiyassat
Date: 2025-02-27
"""

import json
import sys
import subprocess
import os
import pytest


def _run_cli(text: str, extra_args=None):
    """Run the FVAFK CLI and return parsed JSON output."""
    cmd = [
        sys.executable, "-m", "fvafk.cli",
        text,
        "--json",
    ]
    if extra_args:
        cmd.extend(extra_args)

    env = os.environ.copy()
    env["PYTHONPATH"] = os.path.join(
        os.path.dirname(__file__), '..', 'src'
    )
    result = subprocess.run(cmd, capture_output=True, text=True, env=env)
    return json.loads(result.stdout)


class TestCliSyntaxOutput:

    def test_cli_no_morphology_no_syntax_key(self):
        """Running CLI without --morphology should NOT include 'syntax' key."""
        data = _run_cli("كتاب")
        assert "syntax" not in data

    def test_cli_morphology_includes_syntax_key(self):
        """Running CLI with --morphology --json should include 'syntax' key in output."""
        data = _run_cli("كتب الطالب الدرس", extra_args=["--morphology"])
        assert "syntax" in data

    def test_cli_syntax_has_required_structure(self):
        """The 'syntax' key must contain word_forms, links, and violations."""
        data = _run_cli("الكتاب مفيد", extra_args=["--morphology"])
        syntax = data.get("syntax", {})

        assert "word_forms" in syntax, "syntax must have word_forms"
        assert "links" in syntax, "syntax must have links"
        assert "violations" in syntax, "syntax must have violations"

    def test_cli_syntax_links_has_three_types(self):
        """The syntax.links must have isnadi, tadmini, taqyidi keys."""
        data = _run_cli("كتب الطالب الدرس", extra_args=["--morphology"])
        syntax = data.get("syntax", {})
        links = syntax.get("links", {})

        assert "isnadi" in links
        assert "tadmini" in links
        assert "taqyidi" in links

    def test_cli_syntax_violations_is_list(self):
        """The syntax.violations must be a list."""
        data = _run_cli("الكتاب مفيد", extra_args=["--morphology"])
        syntax = data.get("syntax", {})
        assert isinstance(syntax.get("violations"), list)

    def test_cli_syntax_word_forms_is_list(self):
        """syntax.word_forms must be a list."""
        data = _run_cli("الكتاب مفيد", extra_args=["--morphology"])
        syntax = data.get("syntax", {})
        assert isinstance(syntax.get("word_forms"), list)

    def test_cli_backward_compatibility(self):
        """Existing keys in output (c1, c2a, success, input) must still be present."""
        data = _run_cli("كتاب", extra_args=["--morphology"])
        assert "success" in data
        assert "input" in data
        assert "c1" in data
        assert "c2a" in data


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
