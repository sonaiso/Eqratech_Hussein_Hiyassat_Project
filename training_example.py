"""
Complete example demonstrating proper training setup with labels.
This script shows how to:
1. Create a dataset with labels
2. Set up a dataloader
3. Initialize a model and optimizer
4. Run the training loop correctly
"""

import torch
from torch.utils.data import DataLoader
from transformers import AutoTokenizer, AutoModelForSequenceClassification, AdamW
from dataset_with_labels import ArabicTextDataset, validate_dataloader
from train_model import train_model


def main():
    """
    Complete example of training setup and execution.
    """
    print("=" * 70)
    print("Arabic Text Classification Training Example")
    print("=" * 70)
    
    # Configuration
    MODEL_NAME = 'bert-base-arabic'  # or 'aubmindlab/bert-base-arabertv2'
    MAX_LENGTH = 128
    BATCH_SIZE = 8
    LEARNING_RATE = 2e-5
    EPOCHS = 3
    NUM_LABELS = 2  # Binary classification example
    
    # Example data (replace with your actual data)
    # In a real scenario, you would load this from files or databases
    train_texts = [
        "هذا نص عربي إيجابي",
        "نص سلبي للاختبار",
        "مثال آخر للنص الإيجابي",
        "هذا نص سلبي آخر",
        "نص محايد للتدريب",
        "مثال جيد للتصنيف",
        "نص غير جيد للتصنيف",
        "البيانات مهمة للتدريب"
    ]
    
    train_labels = [1, 0, 1, 0, 1, 1, 0, 1]  # 1 = positive, 0 = negative
    
    print(f"\nDataset size: {len(train_texts)} samples")
    print(f"Number of labels: {NUM_LABELS}")
    
    # Step 1: Initialize tokenizer
    print(f"\nLoading tokenizer: {MODEL_NAME}")
    try:
        tokenizer = AutoTokenizer.from_pretrained(MODEL_NAME)
    except Exception as e:
        print(f"Error loading tokenizer: {e}")
        print("Make sure you have internet connection or the model cached locally")
        return
    
    # Step 2: Create dataset with labels
    print("\nCreating dataset with labels...")
    dataset = ArabicTextDataset(
        texts=train_texts,
        labels=train_labels,
        tokenizer=tokenizer,
        max_length=MAX_LENGTH
    )
    
    # Step 3: Create dataloader
    print("Creating dataloader...")
    dataloader = DataLoader(
        dataset,
        batch_size=BATCH_SIZE,
        shuffle=True,
        num_workers=0
    )
    
    # Step 4: Validate dataloader
    print("\nValidating dataloader...")
    if not validate_dataloader(dataloader):
        print("Dataloader validation failed! Please check your dataset implementation.")
        return
    
    # Step 5: Initialize model
    print(f"\nLoading model: {MODEL_NAME}")
    try:
        model = AutoModelForSequenceClassification.from_pretrained(
            MODEL_NAME,
            num_labels=NUM_LABELS
        )
    except Exception as e:
        print(f"Error loading model: {e}")
        print("Make sure you have internet connection or the model cached locally")
        return
    
    # Step 6: Set up device
    device = torch.device('cuda' if torch.cuda.is_available() else 'cpu')
    print(f"\nUsing device: {device}")
    if torch.cuda.is_available():
        print(f"GPU: {torch.cuda.get_device_name(0)}")
    
    # Step 7: Initialize optimizer
    print("\nInitializing optimizer...")
    optimizer = AdamW(model.parameters(), lr=LEARNING_RATE)
    
    # Step 8: Train the model
    print("\n" + "=" * 70)
    print("Starting Training")
    print("=" * 70)
    
    try:
        training_stats = train_model(
            model=model,
            dataloader=dataloader,
            optimizer=optimizer,
            loss_function=None,  # Model computes loss automatically
            device=device,
            epochs=EPOCHS,
            output_dir='./trained_model'
        )
        
        print("\n" + "=" * 70)
        print("Training Completed Successfully!")
        print("=" * 70)
        print(f"\nTraining Statistics:")
        print(f"  Total batches processed: {training_stats['total_batches']}")
        print(f"  Loss per epoch: {training_stats['epoch_losses']}")
        
        if training_stats['epoch_losses']:
            print(f"  Final loss: {training_stats['epoch_losses'][-1]:.4f}")
            print(f"  Average loss: {sum(training_stats['epoch_losses'])/len(training_stats['epoch_losses']):.4f}")
        
    except ValueError as e:
        print(f"\nTraining failed with error: {e}")
        print("\nCommon issues:")
        print("1. Dataset doesn't return 'labels' in __getitem__")
        print("2. Labels have wrong shape or dtype")
        print("3. Model and labels are incompatible")
        return
    except Exception as e:
        print(f"\nUnexpected error during training: {e}")
        import traceback
        traceback.print_exc()
        return


def test_single_batch():
    """
    Test function to verify a single batch works correctly.
    Useful for debugging before running full training.
    """
    print("\n" + "=" * 70)
    print("Testing Single Batch")
    print("=" * 70)
    
    # Simple test data
    test_texts = ["نص تجريبي", "نص آخر"]
    test_labels = [0, 1]
    
    # Initialize
    tokenizer = AutoTokenizer.from_pretrained('bert-base-arabic')
    model = AutoModelForSequenceClassification.from_pretrained('bert-base-arabic', num_labels=2)
    device = torch.device('cuda' if torch.cuda.is_available() else 'cpu')
    model.to(device)
    
    # Create dataset and dataloader
    dataset = ArabicTextDataset(test_texts, test_labels, tokenizer, max_length=64)
    dataloader = DataLoader(dataset, batch_size=2)
    
    # Get one batch
    batch = next(iter(dataloader))
    
    print("\nBatch contents:")
    for key, value in batch.items():
        print(f"  {key}: shape={value.shape}, dtype={value.dtype}")
    
    # Move to device
    input_ids = batch['input_ids'].to(device)
    attention_mask = batch['attention_mask'].to(device)
    token_type_ids = batch['token_type_ids'].to(device)
    labels = batch['labels'].to(device)
    
    # Forward pass
    print("\nRunning forward pass...")
    model.eval()
    with torch.no_grad():
        outputs = model(
            input_ids=input_ids,
            attention_mask=attention_mask,
            token_type_ids=token_type_ids,
            labels=labels
        )
    
    print(f"Loss: {outputs.loss.item():.4f}")
    print(f"Logits shape: {outputs.logits.shape}")
    
    print("\n✓ Single batch test passed!")


if __name__ == "__main__":
    import sys
    
    # Parse command line arguments
    if len(sys.argv) > 1 and sys.argv[1] == '--test':
        # Run single batch test
        test_single_batch()
    else:
        # Run full training
        main()
