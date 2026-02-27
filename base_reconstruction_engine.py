"""
Base class for all reconstruction engines in the Arabic Diana Project.

This module provides a common interface for all engine classes that generate
DataFrames for different grammatical categories (verbs, particles, nouns, etc.).
Each engine must define a SHEET_NAME and implement a make_df() classmethod.
"""

import pandas as pd
from abc import ABC, abstractmethod


class BaseReconstructionEngine(ABC):
    """Abstract base class for all reconstruction engines.
    
    Subclasses must define:
    - SHEET_NAME: str - The name of the Excel sheet for this engine's data
    - make_df: classmethod - A method that returns a pandas DataFrame
    """
    
    SHEET_NAME: str = "UnnamedSheet"
    
    @classmethod
    @abstractmethod
    def make_df(cls) -> pd.DataFrame:
        """Generate and return a DataFrame for this engine's grammatical category.
        
        Returns:
            pd.DataFrame: A DataFrame containing the engine's data with appropriate columns.
        """
        pass
