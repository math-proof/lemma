import Mathlib
import sympy.Basic
import sympy.atlas.LinearAlgebra.Matrix.PerronFrobenius
open Matrix
open MathlibExt.LinearAlgebra.Matrix.PerronFrobeniusWanted


/--
[_root_.Matrix.IsIrreducible.perron_frobenius](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/PerronFrobenius.lean)
-/
@[path]
private lemma Matrix_IsIrreducible_perron_frobenius_eq
  [Fintype n] [DecidableEq n] [Nonempty n]
  {A : Matrix n n ℝ}
-- given
  (hA : A.IsIrreducible) :
-- imply
  ∃ (r : ℝ) (v : n → ℝ),
    0 < r ∧ (∀ i, 0 < v i) ∧ A.mulVec v = r • v ∧
    ∀ μ : ℂ, Matrix.det (μ • (1 : Matrix n n ℂ) - A.map Complex.ofReal) = 0 → ‖μ‖ ≤ r := by
-- proof
  apply Matrix.IsIrreducible.perron_frobenius hA

/--
[perron_frobenius](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/PerronFrobenius.lean)
-/
@[path]
private lemma perron_frobenius_eq
  [Fintype n] [DecidableEq n] [Nonempty n]
  {A : Matrix n n ℝ}
-- given
  (hA : A.IsIrreducible)
  (hA0 : A ≠ 0) :
-- imply
  ∃ (r : ℝ) (v : n → ℝ),
    0 < r ∧ (∀ i, 0 < v i) ∧ A.mulVec v = r • v ∧
    ∀ μ : ℂ, Matrix.det (μ • (1 : Matrix n n ℂ) - toComplexMatrix A) = 0 → ‖μ‖ ≤ r := by
-- proof
  apply MathlibExt.LinearAlgebra.Matrix.PerronFrobeniusWanted.perron_frobenius A hA hA0


-- created on 2026-10-20
