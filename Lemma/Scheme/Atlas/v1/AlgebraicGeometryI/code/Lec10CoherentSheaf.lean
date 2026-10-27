import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.Lec10CoherentSheaf
open AlgebraicGeometry CategoryTheory


/--
[isCoherentModule_iff_finite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec10CoherentSheaf.lean)
-/
@[path]
lemma isCoherentModule_iff_finite
  [CommRing R]
  {M : Type*}
  [AddCommGroup M]
  [Module R M] :
-- imply
  IsCoherentModule R M ↔ Module.Finite R M :=
-- proof
  Iff.rfl

/--
[fg_noetherian_finitePresentation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec10CoherentSheaf.lean)
-/
@[path]
lemma fg_noetherian_finitePresentation
  [CommRing R]
  [IsNoetherianRing R]
  {M : Type*}
  [AddCommGroup M]
  [Module R M]
  [Module.Finite R M] :
-- imply
  Module.FinitePresentation R M :=
-- proof
  Module.finitePresentation_of_finite R M

/--
[isCoherentModule_iff_finitePresentation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec10CoherentSheaf.lean)
-/
@[path]
lemma isCoherentModule_iff_finitePresentation
  [CommRing R]
  [IsNoetherianRing R]
  {M : Type*}
  [AddCommGroup M]
  [Module R M] :
-- imply
  IsCoherentModule R M ↔ Module.FinitePresentation R M :=
-- proof
  (Module.finitePresentation_iff_finite R M).symm


-- created on 2026-10-23
