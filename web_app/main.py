"""FastAPI web application for displaying Arabic grammar activities (improved).
This version loads available engine classes once at application startup,
uses structured Pydantic models for the API response, and logs errors.
"""
from contextlib import asynccontextmanager
from datetime import datetime
from fastapi import FastAPI, Request
from fastapi.responses import HTMLResponse
from fastapi.templating import Jinja2Templates
from pydantic import BaseModel
import logging
import os
from typing import List

logger = logging.getLogger("eqratech")

# Cache of engine classes loaded at startup
ENGINES: List[type] = []

class ActivityOut(BaseModel):
    name: str
    sheet_name: str
    module: str

class ActivitiesResponse(BaseModel):
    date: str
    total_activities: int
    activities: List[ActivityOut]

@asynccontextmanager
async def lifespan(app: FastAPI):
    """Load engine classes once when the application starts.

    This function expects a collect_engines() function available from
    Main_engine.py at the repository root. Run the app with PYTHONPATH=. or
    package the project so that Main_engine is importable.
    """
    try:
        # Import here to fail fast if Main_engine is not available
        from Main_engine import collect_engines
    except Exception as e:
        logger.exception("Failed to import collect_engines. Ensure Main_engine.py is accessible and PYTHONPATH includes project root.")
        # Reraise to make startup fail visibly in logs
        raise

    try:
        engine_classes = collect_engines()
        if not isinstance(engine_classes, (list, tuple)):
            logger.warning("collect_engines did not return a list/tuple. Got: %s", type(engine_classes))
            engine_classes = list(engine_classes)

        for e in engine_classes:
            if isinstance(e, type):
                ENGINES.append(e)
            else:
                logger.warning("collect_engines returned non-class item: %s", type(e))
    except Exception:
        logger.exception("Error while collecting engines")
        raise
    
    yield
    # Cleanup code can go here if needed

app = FastAPI(title="Eqratech Arabic Diana Project - Activities", lifespan=lifespan)

# Load templates from the package templates directory
templates = Jinja2Templates(directory=os.path.join(os.path.dirname(__file__), "templates"))


@app.get("/", response_class=HTMLResponse)
async def home(request: Request):
    today = datetime.now().strftime("%Y-%m-%d")
    activities = [
        {"name": cls.__name__, "sheet_name": getattr(cls, "SHEET_NAME", cls.__name__), "module": cls.__module__}
        for cls in ENGINES
    ]
    return templates.TemplateResponse("index.html", {"request": request, "today": today, "activities": activities, "total_activities": len(activities)})


@app.get("/api/activities", response_model=ActivitiesResponse)
async def get_activities():
    today = datetime.now().strftime("%Y-%m-%d")
    activities = [ActivityOut(name=cls.__name__, sheet_name=getattr(cls, "SHEET_NAME", cls.__name__), module=cls.__module__) for cls in ENGINES]
    return ActivitiesResponse(date=today, total_activities=len(activities), activities=activities)