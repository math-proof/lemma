import Mathlib
import sympy.Basic
import sympy.atlas.GameTheory.ShapleyValue
open MathlibExt.GameTheory.ShapleyValue


/--
[shapley_characterization](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/ShapleyValue.lean)
-/
@[path]
private lemma shapley_characterization_eq
  [DecidableEq Player] [Fintype Player] :
-- imply
  ∃! φ : CoopGame Player →ₗ[ℝ] (Player → ℝ),
    IsEfficient φ ∧ IsSymmetric φ ∧ SatisfiesNullPlayerAxiom φ := by
-- proof
  apply MathlibExt.GameTheory.ShapleyValue.shapley_characterization


-- created on 2026-10-20
