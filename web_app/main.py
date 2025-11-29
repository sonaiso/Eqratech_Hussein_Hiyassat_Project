"""FastAPI web application for Arabic Grammar Activities."""
from __future__ import annotations

import sys
import logging
from contextlib import asynccontextmanager
from datetime import datetime
from pathlib import Path
from typing import List, Any

from fastapi import FastAPI, Request
from fastapi.responses import HTMLResponse
from pydantic import BaseModel

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

# Add parent directory to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

# Global engines cache
ENGINES: List[Any] = []


class ActivityOut(BaseModel):
    """Output model for a single activity."""
    sheet_name: str
    engine_class: str


class ActivitiesResponse(BaseModel):
    """Response model for activities endpoint."""
    date: str
    total_activities: int
    activities: List[ActivityOut]


@asynccontextmanager
async def lifespan(app: FastAPI):
    """Lifespan context manager for startup/shutdown events."""
    global ENGINES
    # Startup: Load engines
    try:
        from Main_engine import collect_engines
        ENGINES = collect_engines()
        logger.info(f"Successfully loaded {len(ENGINES)} engine(s)")
    except ImportError as e:
        logger.error(f"Failed to import Main_engine: {e}")
        ENGINES = []
    except Exception as e:
        logger.error(f"Error loading engines: {e}")
        ENGINES = []
    
    yield
    
    # Shutdown: cleanup if needed
    ENGINES = []


app = FastAPI(
    title="Arabic Grammar Activities",
    description="Web interface for Arabic grammar processing engines",
    version="1.0.0",
    lifespan=lifespan
)


@app.get("/", response_class=HTMLResponse)
async def home(request: Request):
    """Display the main activities page."""
    activities_html = ""
    for engine in ENGINES:
        sheet_name = getattr(engine, 'SHEET_NAME', engine.__name__)
        class_name = engine.__name__
        activities_html += f"""
        <div class="activity-card">
            <h3>{sheet_name}</h3>
            <p class="engine-name">{class_name}</p>
        </div>
        """
    
    if not activities_html:
        activities_html = "<p class='no-activities'>لا توجد أنشطة متاحة حالياً</p>"
    
    html_content = f"""
    <!DOCTYPE html>
    <html lang="ar" dir="rtl">
    <head>
        <meta charset="UTF-8">
        <meta name="viewport" content="width=device-width, initial-scale=1.0">
        <title>الأنشطة النحوية العربية</title>
        <style>
            * {{
                box-sizing: border-box;
                margin: 0;
                padding: 0;
            }}
            body {{
                font-family: 'Segoe UI', Tahoma, Geneva, Verdana, sans-serif;
                background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
                min-height: 100vh;
                padding: 20px;
            }}
            .container {{
                max-width: 1200px;
                margin: 0 auto;
            }}
            header {{
                text-align: center;
                color: white;
                padding: 30px 0;
            }}
            header h1 {{
                font-size: 2.5em;
                margin-bottom: 10px;
                text-shadow: 2px 2px 4px rgba(0,0,0,0.3);
            }}
            header p {{
                font-size: 1.2em;
                opacity: 0.9;
            }}
            .stats {{
                background: white;
                border-radius: 15px;
                padding: 20px;
                margin: 20px 0;
                text-align: center;
                box-shadow: 0 10px 30px rgba(0,0,0,0.2);
            }}
            .stats h2 {{
                color: #667eea;
                font-size: 3em;
            }}
            .stats p {{
                color: #666;
                font-size: 1.1em;
            }}
            .activities-grid {{
                display: grid;
                grid-template-columns: repeat(auto-fill, minmax(280px, 1fr));
                gap: 20px;
                padding: 20px 0;
            }}
            .activity-card {{
                background: white;
                border-radius: 12px;
                padding: 25px;
                box-shadow: 0 5px 20px rgba(0,0,0,0.15);
                transition: transform 0.3s ease, box-shadow 0.3s ease;
            }}
            .activity-card:hover {{
                transform: translateY(-5px);
                box-shadow: 0 15px 40px rgba(0,0,0,0.2);
            }}
            .activity-card h3 {{
                color: #333;
                font-size: 1.3em;
                margin-bottom: 10px;
                border-bottom: 2px solid #667eea;
                padding-bottom: 10px;
            }}
            .activity-card .engine-name {{
                color: #888;
                font-size: 0.9em;
                font-family: monospace;
                background: #f5f5f5;
                padding: 5px 10px;
                border-radius: 5px;
            }}
            .no-activities {{
                text-align: center;
                color: white;
                font-size: 1.5em;
                padding: 50px;
            }}
            .date {{
                color: rgba(255,255,255,0.8);
                font-size: 0.9em;
            }}
        </style>
    </head>
    <body>
        <div class="container">
            <header>
                <h1>🌟 الأنشطة النحوية العربية</h1>
                <p>Arabic Grammar Activities</p>
                <p class="date">{datetime.now().strftime('%Y-%m-%d %H:%M')}</p>
            </header>
            
            <div class="stats">
                <h2>{len(ENGINES)}</h2>
                <p>محرك نحوي متاح | Available Grammar Engines</p>
            </div>
            
            <div class="activities-grid">
                {activities_html}
            </div>
        </div>
    </body>
    </html>
    """
    return HTMLResponse(content=html_content)


@app.get("/api/activities", response_model=ActivitiesResponse)
async def get_activities():
    """Return list of all available grammar activities."""
    activities = []
    for engine in ENGINES:
        sheet_name = getattr(engine, 'SHEET_NAME', engine.__name__)
        activities.append(ActivityOut(
            sheet_name=sheet_name,
            engine_class=engine.__name__
        ))
    
    return ActivitiesResponse(
        date=datetime.now().isoformat(),
        total_activities=len(activities),
        activities=activities
    )


@app.get("/health")
async def health_check():
    """Health check endpoint."""
    return {
        "status": "healthy",
        "engines_loaded": len(ENGINES),
        "timestamp": datetime.now().isoformat()
    }
