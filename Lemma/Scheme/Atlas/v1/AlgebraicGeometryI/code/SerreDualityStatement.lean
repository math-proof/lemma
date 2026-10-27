import Mathlib
import Initialize.Tactic.Attr.Basic
import Structure.v1.Atlas.AlgebraicGeometryI.code.SerreDualityStatement
open SerreDualityStatement


/--
[serre_duality_finrank_general](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityStatement.lean)
-/
@[path]
private lemma serre_duality_finrank_general_eq
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
@[path]
private lemma serre_duality_reverse_finrank_general_eq
  {k : Type u}
  [Field k]
  {X : SmoothCompleteCurveVS k}
  {E : X.LocallyFreeSheaf} :
-- imply
  Module.finrank k (X.H1 E) = Module.finrank k (X.globalSections (X.serreDual E)) := by
-- proof
  apply SerreDualityStatement.serre_duality_reverse_finrank_general X E


-- created on 2026-10-23
