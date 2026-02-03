# Web API Documentation

This document describes the FastAPI web service for the FVAFK Arabic NLP system.

## Running the Server

### Using the Helper Script

```bash
python run_server.py
```

Options:
- `--host HOST`: Host address (default: 127.0.0.1)
- `--port PORT`: Port number (default: 8000)
- `--reload`: Enable auto-reload for development

### Using Environment Variables

You can configure the server using environment variables:

```bash
# Configure CORS origins (comma-separated)
export CORS_ORIGINS="http://localhost:3000,http://localhost:8000"

# Configure host and port
export HOST="0.0.0.0"
export PORT="8080"

python run_server.py
```

### Direct Execution

```bash
python -m web_app.main
```

## API Endpoints

### Health Check

**GET /** or **GET /health**

Returns the API status and version.

```bash
curl http://localhost:8000/
```

Response:
```json
{
  "status": "ok",
  "version": "0.1.0"
}
```

### Text Analysis

**POST /analyze**

Analyzes Arabic text through C1 (encoding) and C2a (phonology) phases, with optional C2b (morphology).

Request body:
```json
{
  "text": "كِتَابٌ",
  "verbose": false,
  "morphology": false,
  "multi_word": false
}
```

Parameters:
- `text` (required): Arabic text to analyze
- `verbose` (optional): Include detailed unit information (default: false)
- `morphology` (optional): Include morphological analysis (default: false)
- `multi_word` (optional): Analyze each word separately (default: false, requires morphology: true)

Example:
```bash
curl -X POST http://localhost:8000/analyze \
  -H "Content-Type: application/json" \
  -d '{"text": "كِتَابٌ"}'
```

Response includes:
- `input`: Original input text
- `success`: Whether analysis succeeded
- `c1`: Encoding phase results (unit count)
- `c2a`: Phonological phase results (gates, syllables)
- `c2b`: Morphological phase results (if morphology=true)
- `stats`: Performance timing information

### Morphological Analysis

**POST /analyze/morphology**

Performs full analysis including morphology (C1 + C2a + C2b phases).

This is equivalent to calling `/analyze` with `morphology: true`.

Request body:
```json
{
  "text": "كَاتِبٌ",
  "verbose": false,
  "multi_word": false
}
```

Example:
```bash
curl -X POST http://localhost:8000/analyze/morphology \
  -H "Content-Type: application/json" \
  -d '{"text": "كَاتِبٌ"}'
```

Response includes all phases (C1, C2a, C2b) with:
- Root extraction (letters, type, length)
- Pattern matching (template, type, category)

### Multi-Word Analysis

For analyzing multiple words in a sentence:

```bash
curl -X POST http://localhost:8000/analyze/morphology \
  -H "Content-Type: application/json" \
  -d '{"text": "كَاتِبٌ وَقَارِئٌ", "multi_word": true}'
```

This will analyze each word separately and return results for each.

## Development

### Running Tests

```bash
# Install test dependencies
pip install -r requirements-dev.txt

# Run web_app tests
PYTHONPATH=src pytest tests/test_web_app.py -v

# Run all tests
PYTHONPATH=src pytest tests/ -v
```

### Interactive API Documentation

When the server is running, you can access:

- **Swagger UI**: http://localhost:8000/docs
- **ReDoc**: http://localhost:8000/redoc

These provide interactive documentation where you can test the API directly from your browser.

## Security Notes

- By default, CORS is configured to allow only localhost origins
- To allow other origins, set the `CORS_ORIGINS` environment variable
- Never use `allow_origins=["*"]` in production
- The API validates all inputs using Pydantic models
- Empty text requests are rejected with a 422 validation error

## Performance

Typical performance on standard hardware:
- C1 (Encoding): ~0.04ms per word
- C2a (Phonology): ~0.12ms per word
- C2b (Morphology): ~1.1ms per word
- Total: ~1.3ms per word

Performance may vary based on text complexity and system resources.
