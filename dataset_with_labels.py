"""
Example dataset implementation with proper label handling for Arabic text classification.
This demonstrates how to create a PyTorch Dataset that returns labels correctly.
"""

import torch
from torch.utils.data import Dataset, DataLoader
from transformers import AutoTokenizer


class ArabicTextDataset(Dataset):
    """
    PyTorch Dataset for Arabic text classification.
    
    This dataset properly implements __getitem__ to return a dictionary with
    'input_ids', 'attention_mask', 'token_type_ids', and 'labels'.
    """
    
    def __init__(self, texts, labels, tokenizer, max_length=128):
        """
        Initialize the dataset.
        
        Args:
            texts (list): List of text strings
            labels (list): List of labels (integers or tensors)
            tokenizer: Tokenizer to use (e.g., from transformers)
            max_length (int): Maximum sequence length
        """
        self.texts = texts
        self.labels = labels
        self.tokenizer = tokenizer
        self.max_length = max_length
        
        # Validate that texts and labels have the same length
        if len(texts) != len(labels):
            raise ValueError(f"Number of texts ({len(texts)}) must match number of labels ({len(labels)})")
    
    def __len__(self):
        """Return the number of samples in the dataset."""
        return len(self.texts)
    
    def __getitem__(self, idx):
        """
        Get a single sample from the dataset.
        
        Args:
            idx (int): Index of the sample
            
        Returns:
            dict: Dictionary containing 'input_ids', 'attention_mask', 
                  'token_type_ids', and 'labels'
        """
        text = self.texts[idx]
        label = self.labels[idx]
        
        # Tokenize the text
        encoding = self.tokenizer(
            text,
            add_special_tokens=True,
            max_length=self.max_length,
            padding='max_length',
            truncation=True,
            return_tensors='pt'
        )
        
        # Return dictionary with all required keys
        return {
            'input_ids': encoding['input_ids'].flatten(),
            'attention_mask': encoding['attention_mask'].flatten(),
            'token_type_ids': encoding['token_type_ids'].flatten(),
            'labels': torch.tensor(label, dtype=torch.long)
        }


class ArabicTextDatasetForTokenClassification(Dataset):
    """
    PyTorch Dataset for Arabic token-level classification (e.g., NER, POS tagging).
    
    This dataset handles token-level labels properly.
    """
    
    def __init__(self, texts, token_labels, tokenizer, max_length=128, label_pad_token_id=-100):
        """
        Initialize the dataset.
        
        Args:
            texts (list): List of text strings or list of token lists
            token_labels (list): List of label sequences (list of lists)
            tokenizer: Tokenizer to use
            max_length (int): Maximum sequence length
            label_pad_token_id (int): ID to use for padding labels (default: -100, ignored by most loss functions)
        """
        self.texts = texts
        self.token_labels = token_labels
        self.tokenizer = tokenizer
        self.max_length = max_length
        self.label_pad_token_id = label_pad_token_id
        
        if len(texts) != len(token_labels):
            raise ValueError(f"Number of texts ({len(texts)}) must match number of label sequences ({len(token_labels)})")
    
    def __len__(self):
        """Return the number of samples in the dataset."""
        return len(self.texts)
    
    def __getitem__(self, idx):
        """
        Get a single sample from the dataset.
        
        Args:
            idx (int): Index of the sample
            
        Returns:
            dict: Dictionary containing 'input_ids', 'attention_mask', 
                  'token_type_ids', and 'labels'
        """
        text = self.texts[idx]
        labels = self.token_labels[idx]
        
        # Tokenize the text
        encoding = self.tokenizer(
            text,
            add_special_tokens=True,
            max_length=self.max_length,
            padding='max_length',
            truncation=True,
            return_tensors='pt',
            is_split_into_words=isinstance(text, list)  # Handle pre-tokenized text
        )
        
        # Align labels with tokenized text
        # This is a simplified version - in practice, you need to handle subword tokenization
        label_ids = []
        for i, label in enumerate(labels):
            if i < self.max_length - 2:  # Account for [CLS] and [SEP]
                label_ids.append(label)
        
        # Add special token labels
        label_ids = [self.label_pad_token_id] + label_ids + [self.label_pad_token_id]
        
        # Pad to max_length
        while len(label_ids) < self.max_length:
            label_ids.append(self.label_pad_token_id)
        
        # Truncate if necessary
        label_ids = label_ids[:self.max_length]
        
        return {
            'input_ids': encoding['input_ids'].flatten(),
            'attention_mask': encoding['attention_mask'].flatten(),
            'token_type_ids': encoding['token_type_ids'].flatten(),
            'labels': torch.tensor(label_ids, dtype=torch.long)
        }


def create_example_dataloader():
    """
    Create an example dataloader with sample Arabic data.
    This demonstrates the proper way to set up a dataloader with labels.
    """
    # Example data (replace with your actual data)
    example_texts = [
        "هذا نص عربي للتدريب",
        "مثال آخر للنص العربي",
        "البيانات يجب أن تحتوي على تسميات"
    ]
    
    example_labels = [0, 1, 0]  # Binary classification example
    
    # Load tokenizer (example using bert-base-arabic)
    # You would need to install transformers: pip install transformers
    try:
        from transformers import AutoTokenizer
        tokenizer = AutoTokenizer.from_pretrained('bert-base-arabic')
        
        # Create dataset
        dataset = ArabicTextDataset(
            texts=example_texts,
            labels=example_labels,
            tokenizer=tokenizer,
            max_length=128
        )
        
        # Create dataloader
        dataloader = DataLoader(
            dataset,
            batch_size=2,
            shuffle=True,
            num_workers=0  # Set to 0 for debugging, increase for production
        )
        
        return dataloader
    except ImportError:
        print("transformers library not installed. Install with: pip install transformers")
        return None


def validate_dataloader(dataloader):
    """
    Validate that a dataloader returns batches with the correct structure.
    
    Args:
        dataloader: DataLoader to validate
    
    Returns:
        bool: True if validation passes, False otherwise
    """
    print("Validating dataloader...")
    
    if len(dataloader) == 0:
        print("ERROR: Dataloader is empty!")
        return False
    
    # Get first batch
    batch = next(iter(dataloader))
    
    # Check required keys
    required_keys = ['input_ids', 'attention_mask', 'token_type_ids', 'labels']
    for key in required_keys:
        if key not in batch:
            print(f"ERROR: Required key '{key}' not found in batch!")
            print(f"Available keys: {list(batch.keys())}")
            return False
    
    print("✓ All required keys present in batch")
    
    # Check that all tensors have the same batch size
    batch_sizes = {key: batch[key].shape[0] for key in required_keys}
    if len(set(batch_sizes.values())) > 1:
        print(f"ERROR: Inconsistent batch sizes: {batch_sizes}")
        return False
    
    print(f"✓ Consistent batch size: {list(batch_sizes.values())[0]}")
    
    # Check tensor shapes
    print("\nBatch tensor shapes:")
    for key in required_keys:
        print(f"  {key}: {batch[key].shape}")
    
    print("\n✓ Dataloader validation passed!")
    return True


if __name__ == "__main__":
    print("Example usage of ArabicTextDataset")
    print("=" * 50)
    
    # Create and validate example dataloader
    dataloader = create_example_dataloader()
    
    if dataloader is not None:
        validate_dataloader(dataloader)
        
        print("\nExample batch:")
        batch = next(iter(dataloader))
        print(f"Input IDs shape: {batch['input_ids'].shape}")
        print(f"Labels shape: {batch['labels'].shape}")
        print(f"Labels: {batch['labels']}")
