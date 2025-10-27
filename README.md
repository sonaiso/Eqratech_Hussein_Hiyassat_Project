# Eqratech Arabic Diana Project

This repository contains a collection of Arabic NLP utilities including generators, analyzers, and CLI tools.

## Getting Started

Install the Python dependencies:

```bash
pip install -r requirements.txt
```

## Running the Unified CLI

The `all_in_one_system_fixed.py` module provides a unified command line interface.  Two subcommands are currently available:

* `phonetics` — run the comprehensive phonetics pipeline on inline text or the Quran dataset.
* `export-grammar` — export the multilayer grammar workbook using the legacy engines.

Example invocations:

```bash
# Analyze inline text and display a pretty report
python all_in_one_system_fixed.py phonetics --text "الطَّالِبُ الْمُجْتَهِدُ يَدْرُسُ فِي الْجَامِعَةِ." --report pretty

# Generate a Markdown report based on a Quran text file (provide your own path)
python all_in_one_system_fixed.py phonetics --quran_file path/to/quran-simple-enhanced.txt --report md --max_chars 6000

# Export the multilayer grammar workbook (default output is full_multilayer_grammar.xlsx)
python all_in_one_system_fixed.py export-grammar --output output.xlsx
```

The phonetics subcommand also supports `--report json` for structured output and `--csv` to export word/syllable summaries.
