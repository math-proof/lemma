module

public import Mathlib
public import Structure.v1.Atlas.AlgebraicGeometryI.code.SerreDualityStatement

public section

open SerreDualityStatement


/--
[serre_duality_finrank_general](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityStatement.lean)
-/
public theorem serre_duality_finrank_general_eq
  {k : Type u}
  [Field k]
  {X : SmoothCompleteCurveVS k}
  {E : X.LocallyFreeSheaf} :
-- imply
  Module.finrank k (X.globalSections E) = Module.finrank k (X.H1 (X.serreDual E)) := by
-- proof
  apply SerreDualityStatement.serre_duality_finrank_general X E

/--
[serre_duality_reverse_finrank_general](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityStatement.lean)
-/
public theorem serre_duality_reverse_finrank_general_eq
  {k : Type u}
  [Field k]
  {X : SmoothCompleteCurveVS k}
  {E : X.LocallyFreeSheaf} :
-- imply
  Module.finrank k (X.H1 E) = Module.finrank k (X.globalSections (X.serreDual E)) := by
-- proof
  apply SerreDualityStatement.serre_duality_reverse_finrank_general X E


-- created on 2026-10-23
