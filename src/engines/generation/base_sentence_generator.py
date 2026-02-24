"""Base class for sentence generators, providing shared utilities."""

import pandas as pd
from typing import List, Optional, Tuple


class BaseSentenceGenerator:
    """
    القاعدة المشتركة لمولدات الجمل.

    توفر وظائف مساعدة مشتركة:
    - __init__: تهيئة قائمة الجمل
    - _get_tool_column: اختيار عمود الأدوات المناسب من DataFrame
    - _build_comp_strings: بناء قائمة وصف المكونات

    يمكن للفئات الفرعية تجاوز MAX_SENTENCES بمتغير الفئة.
    """

    MAX_SENTENCES: int = 5000

    def __init__(self) -> None:
        self.sentences: List[dict] = []

    @staticmethod
    def _get_tool_column(df: pd.DataFrame) -> Optional[str]:
        """Return the name of the tool column in *df*, or None if *df* is empty."""
        if df.empty:
            return None
        possible_columns = ['الأداة', 'الكلمة', 'النص', 'العنصر']
        for col in possible_columns:
            if col in df.columns:
                return col
        return df.columns[0] if len(df.columns) > 0 else None

    @staticmethod
    def _build_comp_strings(components: List[Tuple[str, str]]) -> List[str]:
        """Build ``label=token`` strings from a list of (label, token) pairs."""
        return [f"{label}={token}" for label, token in components]
