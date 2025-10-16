"""
Training script for fine-tuning BERT model on Arabic text data.
This script implements a proper training loop with label handling and loss calculation.
"""

import torch
from tqdm import tqdm
import os


def train_model(model, dataloader, optimizer, loss_function, device, epochs, output_dir=None):
    """
    Train a PyTorch model with proper error handling and label validation.
    
    Args:
        model: The PyTorch model to train
        dataloader: DataLoader providing training batches
        optimizer: Optimizer for training
        loss_function: Loss function to use if model doesn't compute loss automatically
        device: Device to train on (cuda/cpu)
        epochs: Number of training epochs
        output_dir: Optional directory to save the trained model
    
    Returns:
        dict: Training statistics including losses per epoch
    """
    
    # Move model to the selected device
    model.to(device)
    print(f"Using device: {device}")
    
    # Set model to training mode
    model.train()
    
    print("Starting training loop...")
    
    training_stats = {
        'epoch_losses': [],
        'total_batches': 0
    }
    
    # Training loop
    for epoch in range(epochs):
        print(f"\nEpoch {epoch + 1}/{epochs}")
        total_loss = 0
        num_batches = 0
        
        # Validate dataloader is not empty
        if len(dataloader) == 0:
            print(f"Warning: Dataloader is empty. Skipping epoch {epoch + 1}")
            continue
        
        # Iterate over batches in the dataloader
        for batch in tqdm(dataloader, desc=f"Training Epoch {epoch + 1}"):
            # Move batch to device
            input_ids = batch['input_ids'].to(device)
            attention_mask = batch['attention_mask'].to(device)
            token_type_ids = batch['token_type_ids'].to(device)
            
            # Check if labels are present in the batch
            if 'labels' not in batch:
                print("\nError: 'labels' key not found in batch.")
                print("Please ensure your dataset's __getitem__ method returns a dictionary with 'labels' key.")
                print("Training cannot proceed without labels.")
                raise ValueError("Labels are required for training but not found in batch")
            
            # Get labels from batch
            labels = batch['labels'].to(device)
            
            # Zero the gradients
            optimizer.zero_grad()
            
            # Forward pass
            # If using a model like BertForSequenceClassification, it can calculate loss automatically
            # when labels are provided
            try:
                outputs = model(
                    input_ids=input_ids,
                    attention_mask=attention_mask,
                    token_type_ids=token_type_ids,
                    labels=labels
                )
                
                # Check if model computed the loss
                if hasattr(outputs, 'loss') and outputs.loss is not None:
                    loss = outputs.loss
                else:
                    # If model doesn't calculate loss automatically, use the provided loss function
                    if loss_function is None:
                        raise ValueError("Model does not compute loss automatically and no loss_function provided")
                    loss = loss_function(outputs.logits, labels)
                    
            except TypeError:
                # If model doesn't accept labels parameter, compute loss manually
                outputs = model(
                    input_ids=input_ids,
                    attention_mask=attention_mask,
                    token_type_ids=token_type_ids
                )
                if loss_function is None:
                    raise ValueError("Model does not accept labels parameter and no loss_function provided")
                loss = loss_function(outputs.logits, labels)
            
            # Backward pass
            loss.backward()
            
            # Optimizer step
            optimizer.step()
            
            # Accumulate loss
            total_loss += loss.item()
            num_batches += 1
        
        # Print average loss for the epoch
        if num_batches > 0:
            avg_loss = total_loss / num_batches
            print(f"Epoch {epoch + 1} finished. Average Loss: {avg_loss:.4f}")
            training_stats['epoch_losses'].append(avg_loss)
            training_stats['total_batches'] += num_batches
        else:
            print(f"Epoch {epoch + 1} finished. No batches were processed.")
    
    print("\nTraining finished.")
    
    # Save model if output directory is provided
    if output_dir is not None:
        os.makedirs(output_dir, exist_ok=True)
        model_path = os.path.join(output_dir, 'model.pth')
        torch.save(model.state_dict(), model_path)
        print(f"Model saved to {model_path}")
    
    return training_stats


def main():
    """
    Main function demonstrating how to use the training function.
    This is a template that should be customized based on your specific use case.
    """
    # Example usage (commented out as it requires actual data and model setup)
    """
    from transformers import BertForSequenceClassification, AdamW
    from torch.utils.data import DataLoader
    
    # Initialize model
    model = BertForSequenceClassification.from_pretrained('bert-base-arabic', num_labels=2)
    
    # Initialize optimizer
    optimizer = AdamW(model.parameters(), lr=2e-5)
    
    # Set up device
    device = torch.device('cuda' if torch.cuda.is_available() else 'cpu')
    
    # Assume you have a dataset that returns dictionaries with:
    # 'input_ids', 'attention_mask', 'token_type_ids', and 'labels'
    # dataset = YourCustomDataset(...)
    # dataloader = DataLoader(dataset, batch_size=32, shuffle=True)
    
    # Train the model
    EPOCHS = 3
    stats = train_model(
        model=model,
        dataloader=dataloader,
        optimizer=optimizer,
        loss_function=None,  # None if model computes loss automatically
        device=device,
        epochs=EPOCHS,
        output_dir='./model_output'
    )
    
    print(f"Training completed. Final statistics: {stats}")
    """
    print("Training script loaded. Import train_model function to use it.")


if __name__ == "__main__":
    main()
