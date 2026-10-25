import Mathlib
import sympy.Basic
import Def.v1.Atlas.TensorCategories.code.FrobeniusPerron.Part6
import Lemma.Category.Atlas.v1.TensorCategories.code.FrobeniusPerron
open Real FusionRing
open scoped Matrix


/--
[proposition_1_45_15](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Proposition_1_45_15.lean)
-/
@[path]
lemma proposition_1_45_15
  [DecidableEq ι]
  [Fintype ι]
  [Nonempty ι]
  {B : Matrix ι ι ℕ}
  {ev : ℝ}
  {v : ι → ℝ}
  {w : ι → ℝ}
-- given
  (hv_pos : ∀ i, 0 < v i)
  (hv_eig : (B.map (Nat.cast : ℕ → ℝ)).mulVec v = ev • v)
  (hw_pos : ∀ i, 0 < w i)
  (hw_eig : ((B.map (Nat.cast : ℕ → ℝ)) * (B.map (Nat.cast : ℕ → ℝ)).transpose).mulVec w = (ev ^ 2) • w)
  (hPF : ∀ μ : ℂ, IsComplexEigenvalue (B.map (Nat.cast : ℕ → ℝ)) μ → ‖μ‖ ≤ ev)
  (hev_lt : ev < 2) :
-- imply
  ∃ n : ℕ, 2 ≤ n ∧ ev = 2 * cos (π / n) :=
-- proof
  kronecker_eigenvalue_cos B ev v hv_pos hv_eig w hw_pos hw_eig hPF hev_lt


-- created on 2026-10-23
