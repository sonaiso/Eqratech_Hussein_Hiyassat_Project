"""Base class for Arabic grammar reconstruction engines."""
import pandas as pd


class BaseReconstructionEngine:
    """Base class that all engine classes should inherit from.
    
    Subclasses must define:
    - SHEET_NAME: str - The name of the sheet in the Excel export
    - make_df() -> pd.DataFrame - A class method that returns a DataFrame
    """
    
    SHEET_NAME = "Base"
    
    @classmethod
    def make_df(cls) -> pd.DataFrame:
        """Generate and return a DataFrame for this engine.
        
        Should be overridden by subclasses.
        """
        raise NotImplementedError("Subclasses must implement make_df()")
