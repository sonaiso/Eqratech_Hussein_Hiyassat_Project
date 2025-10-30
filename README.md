# Eqratech_Arabic_Diana_Project
Python_NLP Project with all Arabic tools verbs and names

## Features

### View Today's Activities
You can now view all available Arabic grammar engines through a web interface!

**To start the web server:**
```bash
python run_server.py
```

Then open your browser and navigate to: `http://127.0.0.1:8000/`

**API Endpoint:**
- GET `/api/activities` - Returns JSON data with today's date and all available engines

**What you'll see:**
- Today's date
- Total count of available grammar activities (63 engines)
- List of all Arabic grammar engines with their Arabic names
- Beautiful, responsive interface in both Arabic and English

## Installation

Install dependencies:
```bash
pip install -r requirements.txt
```

## Export Grammar Data

To export all grammar data to Excel:
```bash
python Main_engine.py
```
