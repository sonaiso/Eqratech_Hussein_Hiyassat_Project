#!/usr/bin/env python3
"""
Simple test runner for FractalHub tests

This runner adds the project root to sys.path and then runs the tests.
"""

import sys
from pathlib import Path

# Add project root to path
project_root = Path(__file__).parent.parent
sys.path.insert(0, str(project_root))

# Now run pytest
import pytest

if __name__ == "__main__":
    sys.exit(pytest.main(sys.argv[1:]))
