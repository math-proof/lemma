import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.ProjectionTheory.code.Uniformization
open Finset Real UniformSet


namespace UniformSet

/--
[isUniform_iff_uniformFrom_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/Uniformization.lean)
-/
@[path]
lemma isUniform_iff_uniformFrom_zero
  {N m d : ℕ}
  {X : Finset (Fin d → ℕ)} :
-- imply
  IsUniform N m d X ↔ IsUniformFrom N m d 0 X :=
-- proof
  ⟨fun h j _ hj => h j hj, fun h j hj => h j (Nat.zero_le _) hj⟩

end UniformSet

namespace UniformSet

/--
[isUniformFrom_m](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/Uniformization.lean)
-/
@[path]
lemma isUniformFrom_m
  {N m d : ℕ}
  {X : Finset (Fin d → ℕ)} :
-- imply
  IsUniformFrom N m d m X :=
-- proof
  fun _ hj hj' => absurd (Nat.lt_of_lt_of_le hj' hj) (lt_irrefl _)
/-- Pigeon-hole bound: at any fixed scale `k`, the number of distinct
branching values `R_j` taken by the sub-cube counts across the cubes of `X`
is at most `2 d log(N)`. This is the loss factor that appears at each scale
in the Uniformization Lemma. -/

end UniformSet


-- created on 2026-10-23
