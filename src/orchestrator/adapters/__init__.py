# -*- coding: utf-8 -*-
"""Orchestrator adapters — thin wrappers around existing FVAFK/engines modules."""

from .fvafk_runner import run_fvafk_once

__all__ = ["run_fvafk_once"]
