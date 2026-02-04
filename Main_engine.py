import inspect
import importlib
import pkgutil
import pandas as pd
from pathlib import Path
import sys

# Add src to path for proper imports
sys.path.insert(0, str(Path(__file__).parent / 'src'))

from engines.base import BaseReconstructionEngine


def _iter_engine_modules():
    """
    Iterate through engine modules in src/engines/ directory.
    This auto-discovers all engines from the src/engines/ structure.
    """
    engines_dir = Path(__file__).parent / 'src' / 'engines'
    
    # Import all layer modules
    for layer_dir in engines_dir.iterdir():
        if layer_dir.is_dir() and not layer_dir.name.startswith('__'):
            layer_path = f'engines.{layer_dir.name}'
            try:
                layer_module = importlib.import_module(layer_path)
                yield layer_module
            except Exception as e:
                print(f"Warning: Could not import {layer_path}: {e}")
                continue


def collect_engines():
    """
    Collect all engine classes from src/engines/ directory.
    Returns a list of engine classes that inherit from BaseReconstructionEngine.
    """
    engines = []
    
    # Iterate through all layer modules
    for layer_module in _iter_engine_modules():
        # Get all attributes from the layer module
        for attr_name in dir(layer_module):
            try:
                obj = getattr(layer_module, attr_name)
                # Check if it's a class, inherits from BaseReconstructionEngine, and has required methods
                if (inspect.isclass(obj) and 
                    issubclass(obj, BaseReconstructionEngine) and 
                    obj is not BaseReconstructionEngine and
                    hasattr(obj, 'SHEET_NAME') and 
                    hasattr(obj, 'make_df')):
                    engines.append(obj)
            except Exception:
                continue
    
    # Remove duplicates by sheet name, keeping first appearance
    seen = set()
    unique = []
    for e in engines:
        sn = getattr(e, 'SHEET_NAME', e.__name__)
        if sn not in seen:
            unique.append(e)
            seen.add(sn)
    
    return unique


def export_all(output_path: str = 'full_multilayer_grammar.xlsx'):
    engines = collect_engines()
    with pd.ExcelWriter(output_path) as writer:
        for engine_cls in engines:
            try:
                df = engine_cls.make_df()
                sheet = engine_cls.SHEET_NAME[:31]  # Excel sheet name limit
                df.to_excel(writer, sheet_name=sheet, index=False)
            except Exception as e:
                # Optionally: log or collect errors; for now skip failing engine
                continue


def main():
    export_all()


if __name__ == "__main__":
    main()