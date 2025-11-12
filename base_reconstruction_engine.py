"""Base class for reconstruction engines."""


class BaseReconstructionEngine:
    """Base class that all engine classes inherit from.
    
    Each engine should define:
    - SHEET_NAME: str - The name of the sheet in the Excel export
    - make_df() -> pd.DataFrame - Class method that returns a dataframe with the engine's data
    """
    SHEET_NAME = "Base"
    
    @classmethod
    def make_df(cls):
        """Return a pandas DataFrame with the engine's data.
        
        Must be implemented by subclasses.
        """
        raise NotImplementedError(f"{cls.__name__} must implement make_df()")
