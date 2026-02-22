"""
FastAPI application for FVAFK / Bayan Arabic NLP pipeline.

Run with:
    python run_server.py
    # or directly:
    uvicorn web_app.main:app --reload
"""
from __future__ import annotations

from typing import Any, Optional

from fastapi import FastAPI, HTTPException
from pydantic import BaseModel

from fvafk.cli.main import MinimalCLI

app = FastAPI(
    title="FVAFK / Bayan — Arabic NLP API",
    description=(
        "REST API for the FVAFK Arabic NLP pipeline: "
        "encoding (C1), phonological gates (C2a), morphology (C2b)."
    ),
    version="0.1.0",
)

# Initialise once so gate setup cost is paid at startup, not per request.
_cli = MinimalCLI(verbose=False, json_output=True)


class AnalyseRequest(BaseModel):
    text: str
    morphology: bool = False


class AnalyseResponse(BaseModel):
    input: str
    result: dict[str, Any]


@app.get("/", summary="Health check")
def root() -> dict[str, str]:
    """Return service status."""
    return {"status": "ok", "service": "FVAFK Arabic NLP API", "version": "0.1.0"}


@app.get("/health", summary="Health check (alias)")
def health() -> dict[str, str]:
    return {"status": "ok"}


@app.post("/analyse", response_model=AnalyseResponse, summary="Analyse Arabic text")
def analyse(request: AnalyseRequest) -> AnalyseResponse:
    """
    Run the full FVAFK pipeline on the supplied Arabic text.

    - **text**: Arabic text to analyse (with or without diacritics)
    - **morphology**: also run the C2b morphological analyser
    """
    if not request.text or not request.text.strip():
        raise HTTPException(status_code=422, detail="text must not be empty")

    result: Optional[dict[str, Any]] = _cli.run(
        request.text,
        morphology=request.morphology,
    )
    if result is None:
        result = {}
    return AnalyseResponse(input=request.text, result=result)
