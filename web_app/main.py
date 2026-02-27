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

from Main_engine import collect_engines

app = FastAPI(title="Eqratech Arabic Diana Project - Activities")

# Setup templates directory
templates_dir = Path(__file__).parent / "templates"
if not templates_dir.is_dir():
    raise FileNotFoundError(f"Templates directory not found: {templates_dir}")
templates = Jinja2Templates(directory=str(templates_dir))

# Cache engines at startup to avoid repeated expensive module inspection
_cached_engines = collect_engines()


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


@app.get("/", response_class=HTMLResponse)
async def home(request: Request):
    """Display today's activities and available engines."""
    today = datetime.now().strftime("%Y-%m-%d")
    activities = _build_activities_list(_cached_engines)
    
    return templates.TemplateResponse(
        "index.html",
        {
            "request": request,
            "today": today,
            "activities": activities,
            "total_activities": len(activities)
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
