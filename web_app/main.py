"""FastAPI web application for displaying Arabic grammar activities."""
from datetime import datetime
from fastapi import FastAPI, Request
from fastapi.responses import HTMLResponse
from fastapi.templating import Jinja2Templates
import sys
from pathlib import Path

# Add parent directory to path to import Main_engine
sys.path.insert(0, str(Path(__file__).parent.parent))

from Main_engine import collect_engines

app = FastAPI(title="Eqratech Arabic Diana Project - Activities")

# Setup templates directory
templates_dir = Path(__file__).parent / "templates"
templates_dir.mkdir(exist_ok=True)
templates = Jinja2Templates(directory=str(templates_dir))


@app.get("/", response_class=HTMLResponse)
async def home(request: Request):
    """Display today's activities and available engines."""
    today = datetime.now().strftime("%Y-%m-%d")
    engines = collect_engines()
    
    activities = []
    for engine_cls in engines:
        sheet_name = getattr(engine_cls, 'SHEET_NAME', engine_cls.__name__)
        activities.append({
            'name': engine_cls.__name__,
            'sheet_name': sheet_name,
            'module': engine_cls.__module__
        })
    
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
    engines = collect_engines()
    
    activities = []
    for engine_cls in engines:
        sheet_name = getattr(engine_cls, 'SHEET_NAME', engine_cls.__name__)
        activities.append({
            'name': engine_cls.__name__,
            'sheet_name': sheet_name,
            'module': engine_cls.__module__
        })
    
    return {
        "date": today,
        "total_activities": len(activities),
        "activities": activities
    }
