"""
Tests for the web_app FastAPI application.
"""

import sys
from pathlib import Path

import pytest
from fastapi.testclient import TestClient

# Add parent directory to path to import web_app
parent_dir = Path(__file__).parent.parent
if str(parent_dir) not in sys.path:
    sys.path.insert(0, str(parent_dir))

from web_app.main import app


@pytest.fixture
def client():
    """Create a test client for the FastAPI app."""
    return TestClient(app)


def test_health_check(client):
    """Test the health check endpoint."""
    response = client.get("/")
    assert response.status_code == 200
    data = response.json()
    assert data["status"] == "ok"
    assert "version" in data


def test_health_endpoint(client):
    """Test the /health endpoint."""
    response = client.get("/health")
    assert response.status_code == 200
    data = response.json()
    assert data["status"] == "ok"
    assert "version" in data


def test_analyze_basic(client):
    """Test basic text analysis without morphology."""
    response = client.post(
        "/analyze",
        json={"text": "كِتَابٌ"}
    )
    assert response.status_code == 200
    data = response.json()
    assert data["success"] is True
    assert data["input"] == "كِتَابٌ"
    assert "c1" in data
    assert "c2a" in data
    assert "stats" in data


def test_analyze_with_morphology(client):
    """Test text analysis with morphology."""
    response = client.post(
        "/analyze",
        json={"text": "كَاتِبٌ", "morphology": True}
    )
    assert response.status_code == 200
    data = response.json()
    assert data["success"] is True
    assert "c2b" in data
    assert "root" in data["c2b"]


def test_analyze_morphology_endpoint(client):
    """Test the dedicated morphology endpoint."""
    response = client.post(
        "/analyze/morphology",
        json={"text": "كَاتِبٌ"}
    )
    assert response.status_code == 200
    data = response.json()
    assert data["success"] is True
    assert "c2b" in data
    assert "root" in data["c2b"]


def test_analyze_empty_text(client):
    """Test that empty text returns an error."""
    response = client.post(
        "/analyze",
        json={"text": ""}
    )
    assert response.status_code == 422  # Validation error


def test_analyze_multi_word(client):
    """Test multi-word analysis."""
    response = client.post(
        "/analyze",
        json={
            "text": "كَاتِبٌ وَقَارِئٌ",
            "morphology": True,
            "multi_word": True
        }
    )
    assert response.status_code == 200
    data = response.json()
    assert data["success"] is True
    assert "c2b" in data
