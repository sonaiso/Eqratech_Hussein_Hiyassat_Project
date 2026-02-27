import inspect
import importlib
import pkgutil
import pandas as pd
from pathlib import Path

from base_reconstruction_engine import BaseReconstructionEngine


def _iter_engine_modules():
    base_dir = Path(__file__).parent
    for module_info in pkgutil.iter_modules([str(base_dir)]):
        module_name = module_info.name
        if not module_name.endswith('_engine') and not module_name.endswith('_engine'.replace('_', '')):
            # keep only *engine.py style modules by loose heuristic
            pass
        try:
            yield importlib.import_module(module_name)
        except Exception:
            continue


def collect_engines():
    engines = []
    for module in _iter_engine_modules():
        for _, class_obj in inspect.getmembers(module, inspect.isclass):
            if issubclass(class_obj, BaseReconstructionEngine) and class_obj is not BaseReconstructionEngine:
                # Ensure class defines SHEET_NAME and make_df
                if hasattr(class_obj, 'SHEET_NAME') and hasattr(class_obj, 'make_df'):
                    engines.append(class_obj)
    # Remove duplicates by sheet name keeping first appearance
    seen = set()
    unique = []
    for engine in engines:
        sheet_name = getattr(engine, 'SHEET_NAME', engine.__name__)
        if sheet_name not in seen:
            unique.append(engine)
            seen.add(sheet_name)
    return unique


def export_all(output_path: str = 'full_multilayer_grammar.xlsx'):
    engines = collect_engines()
    with pd.ExcelWriter(output_path) as writer:
        for engine_cls in engines:
            try:
                dataframe = engine_cls.make_df()
                sheet = engine_cls.SHEET_NAME[:31]  # Excel sheet name limit
                dataframe.to_excel(writer, sheet_name=sheet, index=False)
            except Exception as error:
                # Optionally: log or collect errors; for now skip failing engine
                continue


def main():
    export_all()


if __name__ == "__main__":
    main()