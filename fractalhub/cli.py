"""
FractalHub CLI Tools

Command-line interface for FractalHub utilities.
"""

import sys
from pathlib import Path


def validate_dictionary():
    """
    Validate FractalHub dictionary from command line.
    
    Usage:
        fractalhub-validate [path/to/dictionary.yaml]
    """
    from fractalhub.dictionary.validator import DictionaryValidator
    
    # Get dictionary path from command line or use default
    if len(sys.argv) > 1:
        dict_path = sys.argv[1]
    else:
        # Default to v02 dictionary
        try:
            import fractalhub
            module_dir = Path(fractalhub.__file__).parent
            dict_path = module_dir / "data" / "fractalhub_dictionary_v02.yaml"
        except Exception:
            print("Error: Could not find default dictionary.")
            print("Usage: fractalhub-validate [path/to/dictionary.yaml]")
            sys.exit(1)
    
    print(f"Validating dictionary: {dict_path}")
    print()
    
    try:
        # Create validator and run validation
        validator = DictionaryValidator(str(dict_path))
        is_valid, errors, warnings = validator.validate()
        
        # Print report
        print(validator.get_report())
        
        # Exit with appropriate code
        sys.exit(0 if is_valid else 1)
    
    except FileNotFoundError as e:
        print(f"❌ Error: {e}")
        sys.exit(1)
    except Exception as e:
        print(f"❌ Unexpected error: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)


if __name__ == "__main__":
    validate_dictionary()
