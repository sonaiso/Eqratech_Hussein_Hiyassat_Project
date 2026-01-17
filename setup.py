"""Setup file for fractalhub package."""
from setuptools import setup, find_packages

setup(
    name="fractalhub",
    version="1.2.0",
    packages=find_packages(),
    install_requires=[
        "pyyaml",
    ],
    python_requires=">=3.8",
)
