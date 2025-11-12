"""FastAPI app for displaying Arabic grammar activities with improved startup and caching."""
from datetime import datetime
import logging
from typing import List
from fastapi import FastAPI, Request
from fastapi.responses import HTMLResponse
from fastapi.templating import Jinja2Templates
from pydantic import BaseModel
from pathlib import Path

logger = logging.getLogger("eqratech")
logging.basicConfig(level=logging.INFO)

app = FastAPI(title="Eqratech Arabic Diana Project - Activities")

# Templates directory (expect templates to exist in the repository)
templates_dir = Path(__file__).parent / "templates"
templates = Jinja2Templates(directory=str(templates_dir))

# Cached engines list (loaded once at startup)
ENGINES: List[type] = []


class Activity(BaseModel):
    name: str
    sheet_name: str
    module: str


class ActivitiesResponse(BaseModel):
    date: str
    total_activities: int
    activities: List[Activity]


@app.on_event("startup")
async def load_engines():
    """Load available engine classes once when the app starts."""
    global ENGINES
    try:
        # Import here so we don't require Main_engine on module import if not running the app
        from Main_engine import collect_engines  # type: ignore

        engines = collect_engines()
        if not isinstance(engines, list):
            logger.warning("collect_engines() did not return a list; got %s", type(engines))
            ENGINES = []
        else:
            # Basic validation: ensure list of classes/objects with __name__
            valid = []
            for e in engines:
                if hasattr(e, "__name__"):
                    valid.append(e)
                else:
                    logger.warning("Ignored invalid engine object: %r", e)
            ENGINES = valid
        logger.info("Loaded %d engines at startup", len(ENGINES))
    except Exception as exc:  # ImportError, NameError, or runtime errors inside collect_engines
        logger.exception("Failed to load engines at startup: %s", exc)
        ENGINES = []


@app.get("/", response_class=HTMLResponse)
async def home(request: Request):
    """Render HTML page with today's activities."""
    today = datetime.now().strftime("%Y-%m-%d")

    activities = []
    for engine_cls in ENGINES:
        sheet_name = getattr(engine_cls, "SHEET_NAME", engine_cls.__name__)
        activities.append({
            "name": engine_cls.__name__,
            "sheet_name": sheet_name,
            "module": engine_cls.__module__,
        })

    return templates.TemplateResponse(
        "index.html",
        {
            "request": request,
            "today": today,
            "activities": activities,
            "total_activities": len(activities),
        },
    )


@app.get("/api/activities", response_model=ActivitiesResponse)
async def get_activities():
    """Return cached activities as JSON."""
    today = datetime.now().strftime("%Y-%m-%d")

    activities = []
    for engine_cls in ENGINES:
        sheet_name = getattr(engine_cls, "SHEET_NAME", engine_cls.__name__)
        activities.append(
            Activity(name=engine_cls.__name__, sheet_name=sheet_name, module=engine_cls.__module__)
        )

    return ActivitiesResponse(date=today, total_activities=len(activities), activities=activities)


# Simple health endpoint
@app.get("/health")
async def health():
    return {"status": "ok", "engines_loaded": len(ENGINES)}


# End of file
