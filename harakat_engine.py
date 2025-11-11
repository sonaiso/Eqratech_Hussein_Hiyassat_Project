"""
Harakat (Diacritical Marks) Engine

This module loads and processes Arabic diacritical marks (harakat) data from CSV files.
It provides the data in a standardized format for use in reconstruction and linguistic analysis.
"""

import os
import pandas as pd
from base_reconstruction_engine import BaseReconstructionEngine


class حركات(BaseReconstructionEngine):
    """Engine for loading and processing Arabic harakat (diacritical marks)."""
    
    SHEET_NAME = 'الحركات'
    
    @classmethod
    def make_df(cls) -> pd.DataFrame:
        """Load harakat data from CSV file.
        
        Tries to load from multiple possible file locations:
        1. Harakat.csv (root directory)
        2. الحركات.csv (root directory)
        3. الحركات_كامل.csv (root directory)
        
        Returns:
            pd.DataFrame: DataFrame containing harakat data with standardized columns.
        """
        base_dir = os.path.dirname(__file__)
        
        # Try different possible CSV filenames
        possible_files = [
            os.path.join(base_dir, 'Harakat.csv'),
            os.path.join(base_dir, 'الحركات.csv'),
            os.path.join(base_dir, 'الحركات_كامل.csv'),
        ]
        
        csv_path = None
        for path in possible_files:
            if os.path.exists(path):
                csv_path = path
                break
        
        if csv_path is None:
            raise FileNotFoundError(
                f"Could not find harakat CSV file. Tried: {possible_files}"
            )
        
        # Load the CSV file
        try:
            df = pd.read_csv(csv_path, dtype=str).fillna('')
        except Exception:
            # Try with UTF-8-BOM encoding if default fails
            df = pd.read_csv(csv_path, dtype=str, encoding='utf-8-sig').fillna('')
        
        # Ensure standard columns exist
        # The harakat CSV may have different column names, so we'll work with what we have
        # but ensure UTF-8 column exists
        if 'UTF-8' not in df.columns:
            # If there's a column with the harakat symbol, generate UTF-8 from it
            symbol_col = None
            for col in ['شكل الحركة', 'الحركة', 'الحركات', 'haraka_symbol']:
                if col in df.columns:
                    symbol_col = col
                    break
            
            if symbol_col:
                def make_utf8(symbol):
                    if not symbol or str(symbol).strip() == '':
                        return ''
                    return str(symbol[:1].encode('utf-8'))
                
                df['UTF-8'] = df[symbol_col].apply(make_utf8)
        
        return df


class HarakatEngine(حركات):
    """Alias for حركات engine using English name."""
    pass
