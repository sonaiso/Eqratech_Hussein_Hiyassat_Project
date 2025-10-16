# Eqratech_Arabic_Diana_Project
Python_NLP Project with all Arabic tools verbs and names

## New Features: Tokenization with Labels for Supervised Learning

This project now includes comprehensive tools for adding labels to tokenized text data, essential for supervised machine learning tasks.

### Quick Start

1. **Using the utility module:**
```python
from tokenization_with_labels import TokenizationWithLabels

tokenizer = TokenizationWithLabels()
tokenized_data = tokenizer.tokenize_with_labels_from_separate_file(
    'quran_data.txt',
    'labels.txt'
)
```

2. **Using the example notebook:**
   - Open `tokenization_with_labels_examples.ipynb` in Jupyter or Google Colab
   - Follow the examples for different label integration methods

### Documentation

- **[TOKENIZATION_LABELS_GUIDE.md](TOKENIZATION_LABELS_GUIDE.md)** - Complete guide on adding labels to tokenized data
- **[tokenization_with_labels.py](tokenization_with_labels.py)** - Python utility module
- **[tokenization_with_labels_examples.ipynb](tokenization_with_labels_examples.ipynb)** - Jupyter notebook with examples
- **[examples/](examples/)** - Sample data files demonstrating different formats

### Supported Methods

1. **Separate Files** - Data and labels in different files
2. **Embedded Labels (CSV)** - Combined data in CSV format
3. **Embedded Labels (JSON)** - Combined data in JSON format
4. **Label Mapping** - Dictionary-based label assignment
5. **Pattern-Based** - Rule-based label derivation

### Integration with Transformers

Works seamlessly with Hugging Face transformers library:
```python
from transformers import AutoTokenizer
from tokenization_with_labels import TokenizationWithLabels

hf_tokenizer = AutoTokenizer.from_pretrained('aubmindlab/bert-base-arabertv2')
tokenizer = TokenizationWithLabels(tokenizer=hf_tokenizer)
```
