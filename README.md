# Eqratech_Arabic_Diana_Project
Python_NLP Project with all Arabic tools verbs and names

## Features

### View Today's Activities
You can now view all available Arabic grammar engines through a web interface.

To start the web server (recommended):
```bash
python run_server.py
```

Or run directly with uvicorn (if you prefer):
```bash
PYTHONPATH=. uvicorn web_app.main:app --reload --host 127.0.0.1 --port 8000
```

Then open your browser and navigate to: `http://127.0.0.1:8000/`

**API Endpoint:**
- GET `/api/activities` - Returns JSON data with today's date and all available engines

**What you'll see:**
- Today's date
- Total count of available grammar activities (63 engines)
- List of all Arabic grammar engines with their Arabic names
- Responsive interface in Arabic (RTL) and English

## Installation

Create and activate a virtual environment, then install dependencies:
```bash
python -m venv venv
source venv/bin/activate  # Windows: venv\Scripts\activate
python -m pip install --upgrade pip
pip install -r requirements.txt
```

## Notes
- Ensure `Main_engine.py` exists in the project root and that it exposes a `collect_engines()` function that returns a list of engine classes. Run the app with `PYTHONPATH=.` (or use the provided `run_server.py`) so `Main_engine` is importable.
- If `collect_engines()` performs expensive operations, the app loads engines once at startup for better performance.
- If you prefer pinned package versions different from the ones above, update `requirements.txt` accordingly.
