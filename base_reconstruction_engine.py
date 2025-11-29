"""Base class for all grammar reconstruction engines."""
from abc import ABC, abstractmethod
import pandas as pd


class BaseReconstructionEngine(ABC):
    """Abstract base class that all grammar engines must inherit from.
    
    Subclasses must define:
        SHEET_NAME: str - Name for the Excel sheet
        make_df() -> pd.DataFrame - Method to generate the data
    """
    
    SHEET_NAME: str = ""
    
    @classmethod
    @abstractmethod
    def make_df(cls) -> pd.DataFrame:
        """Generate and return the DataFrame for this engine."""
        pass
