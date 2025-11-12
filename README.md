# Eqratech_Arabic_Diana_Project
Python NLP project with Arabic grammar engines and tools.

## Features
- View available Arabic grammar engines via a web interface.

## Quick start
1. Create and activate a virtual environment:
```bash
python -m venv venv
source venv/bin/activate  # Windows: venv\Scripts\activate
```
2. Install dependencies:
```bash
pip install -r requirements.txt
```
3. Run the server (recommended):
```bash
python run_server.py
```
Or with uvicorn directly (ensure PYTHONPATH so Main_engine is importable):
```bash
PYTHONPATH=. uvicorn web_app.main:app --reload --host 127.0.0.1 --port 8000
```
4. Open http://127.0.0.1:8000/ in your browser.

## API
GET /api/activities - Returns JSON with today's date, total_activities, and activities list.

## Notes
- Ensure `Main_engine.py` exists at the repository root and exposes `collect_engines()` which returns a list of engine classes.
- The app loads engines once at startup for performance. If `Main_engine.py` is missing or `collect_engines()` raises, the app will start with zero engines and log the error.

---
