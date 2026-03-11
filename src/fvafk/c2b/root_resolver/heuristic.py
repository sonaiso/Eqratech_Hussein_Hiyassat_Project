# -*- coding: utf-8 -*-
"""Re-export heuristic_root and HeuristicResult from heuristic_version for RootResolver."""
from .heuristic_version import HeuristicResult, heuristic_root

__all__ = ["HeuristicResult", "heuristic_root"]
