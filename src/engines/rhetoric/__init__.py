"""Rhetoric-related engines."""

from .extractor import RhetoricSignalsExtractor
from .types import RhetoricSignal
from .istiara_engine import IstiaraEngine
from .kinaya_engine import KinayaEngine
from .jinass_engine import JinassEngine
from .saja_engine import SajaEngine
from .muqabala_engine import MuqabalaEngine
from .ijaz_itnab_engine import IjazItnabEngine
from .qasr_taqdim_engine import QasrTaqdimEngine
from .tibaq_engine import TibaqEngine
from .taraduf_engine import TaradufEngine
from .tashbih_engine import TashbihEngine
from .tibaq_muqabala_engine import TibaqMuqabalaEngine

__all__ = [
    "RhetoricSignalsExtractor",
    "RhetoricSignal",
    "IstiaraEngine",
    "KinayaEngine",
    "JinassEngine",
    "SajaEngine",
    "MuqabalaEngine",
    "IjazItnabEngine",
    "QasrTaqdimEngine",
    "TibaqEngine",
    "TaradufEngine",
    "TashbihEngine",
    "TibaqMuqabalaEngine",
]
