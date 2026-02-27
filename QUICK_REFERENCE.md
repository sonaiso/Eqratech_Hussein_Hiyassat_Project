# Quick Reference: Tokenization with Labels

## Fast Setup

```python
from tokenization_with_labels import TokenizationWithLabels

tokenizer = TokenizationWithLabels()
```

## Choose Your Method

### 1. Separate Files
```python
tokenized_data = tokenizer.tokenize_with_labels_from_separate_file(
    'data.txt', 'labels.txt'
)
```

### 2. CSV with Columns
```python
tokenized_data = tokenizer.tokenize_with_embedded_labels(
    'data.csv',
    text_column='verse',
    label_column='category'
)
```

### 3. JSON Format
```python
tokenized_data = tokenizer.tokenize_with_embedded_labels(
    'data.json',
    text_column='verse',
    label_column='category',
    file_format='json'
)
```

### 4. Label Dictionary
```python
labels = {0: 'label1', 1: 'label2', ...}
tokenized_data = tokenizer.tokenize_with_label_mapping('data.txt', labels)
```

### 5. Custom Function
```python
def get_label(text):
    return 'label' if condition else 'other'

tokenized_data = tokenizer.tokenize_with_pattern_based_labels(
    'data.txt', get_label
)
```

## With Transformers

```python
from transformers import AutoTokenizer

hf_tokenizer = AutoTokenizer.from_pretrained('aubmindlab/bert-base-arabertv2')
tokenizer = TokenizationWithLabels(tokenizer=hf_tokenizer)

# Use any method above
```

## Save Results

```python
# As JSON
tokenizer.save_tokenized_data(tokenized_data, 'output.json', format='json')

# As CSV
tokenizer.save_tokenized_data(tokenized_data, 'output.csv', format='csv')
```

## Output Format

Each item in `tokenized_data` contains:
```python
{
    'text': 'original text',
    'tokens': ['token1', 'token2', ...],
    'label': 'category'
}
```

## Common Issues

**Different file lengths?**
→ Make sure data and labels files have the same number of lines

**Column not found?**
→ Check CSV/JSON column names match exactly

**Encoding errors?**
→ Save files with UTF-8 encoding

## Full Documentation

See `TOKENIZATION_LABELS_GUIDE.md` for complete details and examples.
