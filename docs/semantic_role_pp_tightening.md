# Semantic Role Projection — PP Tightening

PP (prepositional phrase) semantic role projection was tightened using **operator catalog knowledge** instead of hardcoded preposition→role maps.

## Operator loader dependency

- **Module:** `src/orchestrator/operators_semantics/`
- **Loader:** reads from `data/operators_catalog_split_project_enriched.csv` (preferred) or `data/operators_catalog_split_project_with_evidence.csv`.
- **Lookup:** `get_operator_semantic_hints(token_surface)` returns operator_type, semantic_functions, preferred_semantic_role, withhold_location_for, source_file.
- **Usage:** semantic_roles/projector.py uses this lookup for Rule 4 (majrur/preposition) and does not hardcode prep→role in the projector.

## PP rules tightened

| Preposition | Role | Notes |
|-------------|------|--------|
| إلى | GOAL | Medium confidence with structural support. |
| من | SOURCE | Medium confidence. |
| في | LOCATION | Medium; conservative. |
| بـ | INSTRUMENT | Weak; only when structurally supported. |
| **على** | **Not LOCATION by default** | Preferred: GOAL. For abstract object (e.g. الله), assign GOAL (medium) or leave unprojected; never assign LOCATION. |
| كـ | STATE | Weak when applicable. |

## Why "على" is treated conservatively

- The operator catalog describes على as "للدلالة على الاستعلاء" (spatial).
- In phrases like "على الله" (reliance, obligation), the object is abstract; LOCATION is inappropriate.
- The projector uses operator hints and a small withhold list (e.g. الله): for such objects it assigns GOAL or leaves the role unprojected instead of LOCATION.

## Explainability

- Evidence trace states when operator catalog was used for PP role projection.
- Claims include: "GOAL inferred from preposition (e.g. إلى or على) with governed PP structure", "SOURCE inferred from preposition من", "LOCATION inferred conservatively from في", "Operator semantic hints from enriched operator catalog used for PP role projection."

## Limitations

- Place-like vs abstract object detection is limited to a small withhold list.
- ب can be oath (قسم); INSTRUMENT is only assigned when structurally plausible.
- No deep semantics or world knowledge; structural and catalog-based only.
