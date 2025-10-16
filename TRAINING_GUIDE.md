# Training Loop Implementation Guide

This document explains the proper implementation of a training loop with label handling for Arabic text classification using PyTorch and Transformers.

## Problem Statement

The original training code had several issues:

1. **Missing Labels**: The code checked if labels exist but continued training without them using dummy targets
2. **Conditional Training**: Optimizer and backward pass only executed when labels were present
3. **Inconsistent Error Handling**: The loop would continue even when labels were missing
4. **Dummy Loss Calculation**: Used placeholder loss calculation that wouldn't train the model properly

## Solution

We've implemented three Python modules that fix these issues:

### 1. `train_model.py` - Core Training Function

A robust training function that:
- ✅ Validates labels are present before starting training
- ✅ Raises clear errors if labels are missing
- ✅ Properly handles both models that compute loss automatically and those that don't
- ✅ Consistently applies optimizer steps for all batches
- ✅ Provides training statistics and progress tracking
- ✅ Optionally saves trained models

**Usage:**
```python
from train_model import train_model

stats = train_model(
    model=model,
    dataloader=dataloader,
    optimizer=optimizer,
    loss_function=None,  # or provide custom loss function
    device=device,
    epochs=EPOCHS,
    output_dir='./model_output'
)
```

### 2. `dataset_with_labels.py` - Dataset Implementation

Proper dataset classes that demonstrate how to return labels correctly:

- **`ArabicTextDataset`**: For sequence classification (sentiment analysis, topic classification, etc.)
- **`ArabicTextDatasetForTokenClassification`**: For token-level tasks (NER, POS tagging, etc.)
- **`validate_dataloader()`**: Utility function to verify your dataloader is set up correctly

**Key Features:**
```python
class ArabicTextDataset(Dataset):
    def __getitem__(self, idx):
        # ... tokenization code ...
        return {
            'input_ids': encoding['input_ids'].flatten(),
            'attention_mask': encoding['attention_mask'].flatten(),
            'token_type_ids': encoding['token_type_ids'].flatten(),
            'labels': torch.tensor(label, dtype=torch.long)  # ✅ Labels included!
        }
```

### 3. `training_example.py` - Complete Example

A full working example showing:
- Dataset creation with labels
- Dataloader setup
- Model initialization
- Training execution
- Error handling

**Run the example:**
```bash
# Full training example
python training_example.py

# Single batch test (for debugging)
python training_example.py --test
```

## Updated Notebook Cell

The `connect.ipynb` notebook has been updated with a new cell that demonstrates the proper training loop implementation. The key improvements:

```python
# ✅ FIXED: Check for labels and raise error if missing
if 'labels' not in batch:
    raise ValueError(
        "Labels are required for training but not found in batch. "
        "Please update your dataset's __getitem__ method to include 'labels'."
    )

labels = batch['labels'].to(device)

# ✅ FIXED: Always zero gradients
optimizer.zero_grad()

# ✅ FIXED: Always perform forward pass with labels
outputs = model(
    input_ids=input_ids,
    attention_mask=attention_mask,
    token_type_ids=token_type_ids,
    labels=labels
)

loss = outputs.loss

# ✅ FIXED: Always perform backward pass
loss.backward()

# ✅ FIXED: Always update weights
optimizer.step()
```

## How to Use in Your Project

### Step 1: Ensure Your Dataset Returns Labels

Update your custom dataset's `__getitem__` method to include labels:

```python
def __getitem__(self, idx):
    # ... your tokenization code ...
    
    return {
        'input_ids': ...,
        'attention_mask': ...,
        'token_type_ids': ...,
        'labels': torch.tensor(your_label, dtype=torch.long)  # Add this!
    }
```

### Step 2: Validate Your Dataloader

Before training, validate your dataloader:

```python
from dataset_with_labels import validate_dataloader

if validate_dataloader(dataloader):
    print("✓ Dataloader is properly configured")
else:
    print("✗ Fix your dataloader before training")
```

### Step 3: Use the Training Function

```python
from train_model import train_model

# Initialize your model, optimizer, and dataloader
# ...

# Train
stats = train_model(
    model=model,
    dataloader=dataloader,
    optimizer=optimizer,
    loss_function=None,
    device=device,
    epochs=3,
    output_dir='./output'
)
```

## Key Points to Remember

1. **Labels are Required**: Training cannot proceed without labels in your dataset
2. **Consistent Execution**: All batches must execute the full forward/backward pass
3. **No Dummy Data**: Never use dummy targets or skip backpropagation
4. **Validate Early**: Use `validate_dataloader()` to catch issues before training
5. **Error Messages**: Clear errors help you identify and fix issues quickly

## Requirements

Make sure you have the required packages installed:

```bash
pip install torch transformers tqdm
```

For the example to work, you'll also need:
```bash
pip install datasets tokenizers
```

## Common Errors and Solutions

### Error: "Labels are required for training but not found in batch"

**Solution:** Update your dataset's `__getitem__` method to include 'labels' in the returned dictionary.

### Error: "Number of texts must match number of labels"

**Solution:** Ensure your text list and label list have the same length.

### Error: Model doesn't accept labels parameter

**Solution:** Provide a custom `loss_function` parameter to `train_model()`.

## Files Created

1. `train_model.py` - Core training function
2. `dataset_with_labels.py` - Dataset implementations with labels
3. `training_example.py` - Complete working example
4. `TRAINING_GUIDE.md` - This documentation file
5. Updated `connect.ipynb` - Notebook with proper training cell

## Next Steps

1. Replace example data with your actual dataset
2. Adjust hyperparameters (batch size, learning rate, epochs)
3. Add validation loop for model evaluation
4. Implement early stopping and model checkpointing
5. Add logging and experiment tracking

For more information, see the comments in each module and refer to the [Transformers documentation](https://huggingface.co/docs/transformers/).
