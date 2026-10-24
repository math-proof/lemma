import Mathlib
import sympy.Basic
open AlgebraicGeometry CategoryTheory Limits


namespace ProjectiveComplete

/--
[proj_isProper](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ProjectiveComplete.lean)
-/
@[path]
lemma proj_isProper
  [CommRing A]
  [SetLike σ A]
  [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ}
  [GradedRing 𝒜]
  [Algebra.FiniteType (𝒜 0) A] :
-- imply
  IsProper (Proj.toSpecZero 𝒜) :=
-- proof
  inferInstance

end ProjectiveComplete


-- created on 2026-10-23
