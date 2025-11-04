from abc import ABC, abstractmethod
import pandas as pd


class BaseReconstructionEngine(ABC):
    """Minimal base class for reconstruction engines.

    Engines in this repo should subclass this and implement a classmethod
    `make_df()` that returns a pandas.DataFrame. `SHEET_NAME` should be
    provided as a class attribute.
    """

    SHEET_NAME = None

    @classmethod
    @abstractmethod
    def make_df(cls) -> pd.DataFrame:
        """Return a pandas DataFrame describing the engine's rows.

        Engines should prefer returning `reconstruct_from_base_df(df)` to
        ensure consistent UTF-8/Unicode/phoneme handling.
        """
        raise NotImplementedError()
