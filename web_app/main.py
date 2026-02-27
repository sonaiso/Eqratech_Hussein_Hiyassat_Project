"""
Web application for the Arabic Diana Project.

This FastAPI application provides endpoints to interact with the Arabic grammar
reconstruction engines and provides linguistic analysis capabilities.
"""

from fastapi import FastAPI, HTTPException
from fastapi.responses import JSONResponse
from typing import List, Dict, Any
import sys
import os

# Add parent directory to path to import engines
sys.path.insert(0, os.path.dirname(os.path.dirname(__file__)))

from Main_engine import collect_engines

app = FastAPI(
    title="Eqratech Arabic Diana Project",
    description="Arabic NLP Project with all Arabic tools, verbs and names",
    version="1.0.0"
)


@app.get("/")
async def root():
    """Root endpoint with API information."""
    return {
        "message": "Welcome to Eqratech Arabic Diana Project API",
        "version": "1.0.0",
        "endpoints": {
            "engines": "/engines - List all available grammar engines",
            "engine_data": "/engines/{sheet_name} - Get data for a specific engine",
            "health": "/health - Health check endpoint"
        }
    }


@app.get("/health")
async def health_check():
    """Health check endpoint."""
    return {"status": "healthy", "service": "arabic-diana-api"}


@app.get("/engines")
async def list_engines() -> List[Dict[str, str]]:
    """List all available grammar reconstruction engines.
    
    Returns:
        List of dictionaries containing engine information.
    """
    try:
        engines = collect_engines()
        engine_list = [
            {
                "name": engine.__name__,
                "sheet_name": engine.SHEET_NAME,
                "class": engine.__name__
            }
            for engine in engines
        ]
        return engine_list
    except Exception as e:
        raise HTTPException(status_code=500, detail=f"Error collecting engines: {str(e)}")


@app.get("/engines/{sheet_name}")
async def get_engine_data(sheet_name: str, limit: int = 100):
    """Get data from a specific engine by sheet name.
    
    Args:
        sheet_name: The name of the engine's sheet
        limit: Maximum number of rows to return (default: 100, max: 1000)
        
    Returns:
        Dictionary containing the engine data.
    """
    try:
        # Limit the maximum rows returned
        limit = min(limit, 1000)
        
        engines = collect_engines()
        
        # Find the engine with matching sheet name
        target_engine = None
        for engine in engines:
            if engine.SHEET_NAME == sheet_name:
                target_engine = engine
                break
        
        if target_engine is None:
            raise HTTPException(
                status_code=404,
                detail=f"Engine with sheet name '{sheet_name}' not found"
            )
        
        # Generate the dataframe
        df = target_engine.make_df()
        
        # Convert to dictionary format and limit rows
        data = df.head(limit).to_dict(orient='records')
        
        return {
            "sheet_name": sheet_name,
            "engine": target_engine.__name__,
            "total_rows": len(df),
            "returned_rows": len(data),
            "data": data
        }
    except HTTPException:
        raise
    except Exception as e:
        raise HTTPException(
            status_code=500,
            detail=f"Error generating engine data: {str(e)}"
        )


@app.get("/export/all")
async def export_all_engines():
    """Trigger export of all engines to Excel file.
    
    Returns:
        Status message about the export operation.
    """
    try:
        from Main_engine import export_all
        
        output_path = os.path.join(
            os.path.dirname(os.path.dirname(__file__)),
            'full_multilayer_grammar.xlsx'
        )
        
        export_all(output_path)
        
        return {
            "status": "success",
            "message": "All engines exported successfully",
            "output_file": output_path
        }
    except Exception as e:
        raise HTTPException(
            status_code=500,
            detail=f"Error exporting engines: {str(e)}"
        )
