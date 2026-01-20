"""
Setup script for FractalHub (backward compatibility).

For modern installation, use pyproject.toml with pip install.
"""

from setuptools import setup

# Read long description from README
with open("README.md", "r", encoding="utf-8") as fh:
    long_description = fh.read()

setup(
    name="fractalhub",
    version="1.2.0",
    long_description=long_description,
    long_description_content_type="text/markdown",
)
