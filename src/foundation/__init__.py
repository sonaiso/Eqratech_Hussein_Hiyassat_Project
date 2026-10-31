"""
حزمة الأساس الرياضي — Foundation Package
==========================================
النسخة العملية v0.1 من «الوثيقة الرياضية التأسيسية للعقل الباني».

تُصدِّر الأنواع والأدوات الأساسية للاستخدام من الخارج:

    from foundation import KnowledgeUniverse, Reality, Trace, trace_fn
    from foundation import Shahada, Hypothesis, EpistemicZero
    from foundation import ArabicText, AnalysisPipeline
"""

from .ontology import KnowledgeUniverse, Reality, Trace, trace_fn
from .outputs import Shahada, Hypothesis, EpistemicZero, SystemOutput, OutputKind
from .nuclei import (
    Nucleus,
    ShahadaNucleus,
    SifrNucleus,
    FaradiyyaNucleus,
    TransitionGateNucleus,
    TasawwurNucleus,
    MafhumNucleus,
    MajalNucleus,
    DalalaNucleus,
    NisbaNucleus,
    HukmNucleus,
    TahqiqManatNucleus,
    QiyasNucleus,
    MiataamilNucleus,
    IrabVectorNucleus,
    IfadaNucleus,
    AatharHukmNucleus,
    TaarudTarjihNucleus,
    AhliyyaNucleus,
    WaqiaNucleus,
    LowerLayersNucleus,
)
from .unicode_units import ArabicUnit, ArabicText, UnitKind
from .trace import TraceExtractor
from .pipeline import (
    PipelineStage,
    StagedAnalysis,
    AnalysisPipeline,
    STAGE_NAMES_AR,
    STAGE_NAMES_EN,
)
from .serialization import serialize_analysis, load_analysis

__all__ = [
    # Ontology
    "KnowledgeUniverse",
    "Reality",
    "Trace",
    "trace_fn",
    # Outputs
    "Shahada",
    "Hypothesis",
    "EpistemicZero",
    "SystemOutput",
    "OutputKind",
    # Nuclei
    "Nucleus",
    "ShahadaNucleus",
    "SifrNucleus",
    "FaradiyyaNucleus",
    "TransitionGateNucleus",
    "TasawwurNucleus",
    "MafhumNucleus",
    "MajalNucleus",
    "DalalaNucleus",
    "NisbaNucleus",
    "HukmNucleus",
    "TahqiqManatNucleus",
    "QiyasNucleus",
    "MiataamilNucleus",
    "IrabVectorNucleus",
    "IfadaNucleus",
    "AatharHukmNucleus",
    "TaarudTarjihNucleus",
    "AhliyyaNucleus",
    "WaqiaNucleus",
    "LowerLayersNucleus",
    # Unicode
    "ArabicUnit",
    "ArabicText",
    "UnitKind",
    # Trace
    "TraceExtractor",
    # Pipeline
    "PipelineStage",
    "StagedAnalysis",
    "AnalysisPipeline",
    "STAGE_NAMES_AR",
    "STAGE_NAMES_EN",
    # Serialization
    "serialize_analysis",
    "load_analysis",
]
