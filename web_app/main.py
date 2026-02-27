"""
Arabic Grammar Web Classifier - Main FastAPI Application

This module provides a web API for the Arabic grammar classification system.
"""

from fastapi import FastAPI
from fastapi.responses import JSONResponse

app = FastAPI(
    title="Arabic Grammar Classifier",
    description="API for Arabic NLP grammar classification and analysis",
    version="1.0.0"
)


@app.get("/")
async def root():
    """Root endpoint - provides basic API information."""
    return {
        "message": "مرحبا بك في نظام تصنيف القواعد العربية",
        "message_en": "Welcome to the Arabic Grammar Classifier",
        "version": "1.0.0",
        "endpoints": {
            "/": "This information page",
            "/health": "Health check endpoint",
            "/docs": "API documentation (Swagger UI)",
            "/redoc": "API documentation (ReDoc)"
        }
    }


@app.get("/health")
async def health_check():
    """Health check endpoint."""
    return {
        "status": "healthy",
        "service": "Arabic Grammar Classifier"
    }
