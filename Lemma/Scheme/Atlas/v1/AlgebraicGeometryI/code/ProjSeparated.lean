import Mathlib
import Initialize.Tactic.Attr.Basic
open AlgebraicGeometry


/--
[lemma18_proj_isSeparated](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ProjSeparated.lean)
-/
@[path]
lemma lemma18_proj_isSeparated
  [CommRing A]
  [SetLike σ A]
  [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ}
  [GradedRing 𝒜] :
-- imply
  IsSeparated (Proj.toSpecZero 𝒜) :=
-- proof
  Proj.isSeparated 𝒜


-- created on 2026-10-23
