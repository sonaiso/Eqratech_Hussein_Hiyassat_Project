"""FastAPI web application for displaying Arabic grammar activities."""
from datetime import datetime
from fastapi import FastAPI, Request
from fastapi.responses import HTMLResponse
from fastapi.templating import Jinja2Templates
import sys
from pathlib import Path

# Ensure the parent directory is in PYTHONPATH to import Main_engine.
# (Recommended: run with `PYTHONPATH=.. uvicorn web_app.main:app`)
sys.path.insert(0, str(Path(__file__).parent.parent))

from fastapi import FastAPI, HTTPException
from fastapi.responses import FileResponse, JSONResponse
from fastapi.staticfiles import StaticFiles
from pydantic import BaseModel, Field

app = FastAPI(title="Eqratech Arabic Diana Project - Activities")

# Setup templates directory
templates_dir = Path(__file__).parent / "templates"
if not templates_dir.is_dir():
    raise FileNotFoundError(f"Templates directory not found: {templates_dir}")
templates = Jinja2Templates(directory=str(templates_dir))

# Cache engines at startup to avoid repeated expensive module inspection
_cached_engines = collect_engines()

# Serve the static web interface
_static_dir = os.path.join(os.path.dirname(__file__), "static")
app.mount("/static", StaticFiles(directory=_static_dir), name="static")


def _build_activities_list(engines):
    """Build activities list from engine classes."""
    activities = []
    for engine_cls in engines:
        sheet_name = getattr(engine_cls, 'SHEET_NAME', engine_cls.__name__)
        activities.append({
            'name': engine_cls.__name__,
            'sheet_name': sheet_name,
            'module': engine_cls.__module__
        })
    return activities


class HealthResponse(BaseModel):
    status: str
    version: str


# ---------------------------------------------------------------------------
# Routes
# ---------------------------------------------------------------------------

@app.get("/", summary="Web UI", include_in_schema=False)
def index() -> FileResponse:
    """Serve the Arabic NLP inspection and verification web interface."""
    return FileResponse(os.path.join(_static_dir, "index.html"))


@app.get("/health", response_model=HealthResponse, summary="Health check")
def health() -> HealthResponse:
    """Return service health status."""
    return HealthResponse(status="ok", version="0.1.0")


@app.post("/analyze", summary="Analyze Arabic text")
def analyze(request: AnalyzeRequest) -> Dict[str, Any]:
    """
    Run the FVAFK pipeline on the supplied Arabic text.

    - **text**: The Arabic text to process (with or without diacritics).
    - **morphology**: When ``true``, the C2b morphological layer is included.

    Returns a JSON object with ``c1``, ``c2a``, optional ``c2b``, and ``stats``
    keys — identical to the CLI ``--json`` output.
    """
    try:
        from fvafk.c1 import C1Encoder
        from fvafk.c2a import (
            GateDeletion,
            GateEpenthesis,
            GateFramework,
            GateHamza,
            GateIdgham,
            GateMadd,
            GateShadda,
            GateSukun,
            GateWasl,
        )
    except ImportError as exc:  # pragma: no cover
        raise HTTPException(
            status_code=503,
            detail=f"FVAFK library not available: {exc}",
        ) from exc

    start = time.perf_counter()

    # C1 encoding
    t0 = time.perf_counter()
    encoder = C1Encoder()
    units = encoder.encode(request.text)
    c1_ms = (time.perf_counter() - t0) * 1000

    # C2a phonological gates
    t0 = time.perf_counter()
    gates = [
        GateSukun(), GateShadda(), GateHamza(),
        GateIdgham(), GateMadd(), GateDeletion(),
        GateEpenthesis(), GateWasl(),
    ]
    framework = GateFramework(gates)
    _, gate_results = framework.run(units)
    c2a_ms = (time.perf_counter() - t0) * 1000

    result: Dict[str, Any] = {
        "input": request.text,
        "c1": {"num_units": len(units)},
        "c2a": {
            "gates": [
                {
                    "gate": r.gate_id or type(g).__name__,
                    "status": r.status.name,
                }
                for g, r in zip(gates, gate_results)
            ],
        },
        "stats": {
            "c1_time_ms": round(c1_ms, 3),
            "c2a_time_ms": round(c2a_ms, 3),
            "total_time_ms": round((time.perf_counter() - start) * 1000, 3),
            "gates_count": len(gates),
        },
    }

    # Optional C2b morphological analysis
    if request.morphology:
        from fvafk.c2b import PatternMatcher, RootExtractor
        t0 = time.perf_counter()
        extractor = RootExtractor()
        matcher = PatternMatcher()
        root = extractor.extract(request.text)
        pattern = matcher.match(request.text, root) if root else None
        c2b_ms = (time.perf_counter() - t0) * 1000
        result["c2b"] = {
            "root": " ".join(root.letters) if root else None,
            "pattern": pattern.template if pattern else None,
        }
    )


@app.get("/api/activities")
async def get_activities():
    """Get list of available activities as JSON."""
    today = datetime.now().strftime("%Y-%m-%d")
    activities = _build_activities_list(_cached_engines)
    
    return {
        "date": today,
        "total_activities": len(activities),
        "activities": activities
    }
