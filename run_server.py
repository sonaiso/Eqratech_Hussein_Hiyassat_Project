"""Run the FastAPI app with uvicorn."""
import uvicorn

if __name__ == "__main__":
    # Run with reload=True for development, host=127.0.0.1 for local access only, port=8000 as default
    uvicorn.run("web_app.main:app", host="127.0.0.1", port=8000, reload=True)