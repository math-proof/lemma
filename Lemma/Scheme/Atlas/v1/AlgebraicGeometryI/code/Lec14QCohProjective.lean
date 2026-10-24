import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.Lec14QCohProjective
open CategoryTheory Limits TopologicalSpace AlgebraicGeometry GrMod


/--
[Hom.ext](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec14QCohProjective.lean)
-/
@[path]
private lemma ext_eq
  {A : Type u}
  [CommRing A]
  {σ : Type u}
  [SetLike σ A]
  {M N : GrMod 𝒜}
  {f g : Hom M N}
-- given
  (h : f.toLinearMap = g.toLinearMap) :
-- imply
  f = g := by
-- proof
  apply GrMod.Hom.ext h


-- created on 2026-10-23
