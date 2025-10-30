"""Base class for reconstruction engines."""


class BaseReconstructionEngine:
    """Base class for all reconstruction engines."""
    
    SHEET_NAME = 'Base'
    
    @classmethod
    def make_df(cls):
        """Generate and return a DataFrame for this engine.
        
        Subclasses must implement this method.
        """
        raise NotImplementedError(f"{cls.__name__} must implement make_df()")
