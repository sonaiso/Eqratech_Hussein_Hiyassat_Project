"""
FastAPI web application for FVAFK Arabic NLP system.

This module provides a REST API for Arabic text processing including:
- Text encoding (C1 phase)
- Phonological analysis (C2a phase)  
- Morphological analysis (C2b phase)
"""

from __future__ import annotations

import sys
from pathlib import Path
from typing import Any, Dict, Optional

from fastapi import FastAPI, HTTPException
from fastapi.middleware.cors import CORSMiddleware
from pydantic import BaseModel, Field

# Add src to path to import fvafk modules
src_path = Path(__file__).parent.parent / "src"
if str(src_path) not in sys.path:
    sys.path.insert(0, str(src_path))

from fvafk.cli.main import MinimalCLI

# Create FastAPI app
app = FastAPI(
    title="FVAFK Arabic NLP API",
    description="Arabic phonological and morphological analysis API",
    version="0.1.0",
)

# Add CORS middleware
app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)

# Initialize CLI processor
cli = MinimalCLI()


# Request/Response models
class AnalyzeRequest(BaseModel):
    """Request model for text analysis."""
    
    text: str = Field(..., description="Arabic text to analyze", min_length=1)
    verbose: bool = Field(False, description="Include detailed unit information")
    morphology: bool = Field(False, description="Include morphological analysis")
    multi_word: bool = Field(False, description="Analyze each word separately (requires morphology=True)")


class HealthResponse(BaseModel):
    """Health check response."""
    
    status: str
    version: str


@app.get("/", response_model=HealthResponse)
async def health_check() -> Dict[str, str]:
    """
    Health check endpoint.
    
    Returns:
        Status and version information
    """
    return {
        "status": "ok",
        "version": "0.1.0"
    }


@app.get("/health", response_model=HealthResponse)
async def health() -> Dict[str, str]:
    """
    Alternative health check endpoint.
    
    Returns:
        Status and version information
    """
    return {
        "status": "ok",
        "version": "0.1.0"
    }


@app.post("/analyze")
async def analyze_text(request: AnalyzeRequest) -> Dict[str, Any]:
    """
    Analyze Arabic text through C1 (encoding) and C2a (phonology) phases.
    
    Args:
        request: Analysis request containing text and options
        
    Returns:
        Analysis results including encoding, phonology, and optional morphology
        
    Raises:
        HTTPException: If analysis fails
    """
    try:
        result = cli.run(
            text=request.text,
            verbose=request.verbose,
            morphology=request.morphology,
            multi_word=request.multi_word
        )
        return result
    except Exception as e:
        raise HTTPException(
            status_code=500,
            detail=f"Analysis failed: {str(e)}"
        )


@app.post("/analyze/morphology")
async def analyze_morphology(request: AnalyzeRequest) -> Dict[str, Any]:
    """
    Analyze Arabic text with full morphological analysis.
    
    This endpoint runs all three phases:
    - C1: Text encoding
    - C2a: Phonological analysis
    - C2b: Morphological analysis (root extraction + pattern matching)
    
    Args:
        request: Analysis request containing text and options
        
    Returns:
        Complete analysis results including morphology
        
    Raises:
        HTTPException: If analysis fails
    """
    try:
        result = cli.run(
            text=request.text,
            verbose=request.verbose,
            morphology=True,
            multi_word=request.multi_word
        )
        return result
    except Exception as e:
        raise HTTPException(
            status_code=500,
            detail=f"Morphological analysis failed: {str(e)}"
        )


if __name__ == "__main__":
    import uvicorn
    uvicorn.run(app, host="127.0.0.1", port=8000)
