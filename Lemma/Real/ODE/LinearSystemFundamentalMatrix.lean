import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.ODE.LinearSystemFundamentalMatrix
open MeasureTheory
open MathlibExt.Analysis.ODE.LinearSystemFundamentalMatrixWanted


/--
[_root_.ODE.existsUnique_hasDerivAt_eq_continuousLinearMap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/ODE/LinearSystemFundamentalMatrix.lean)
-/
@[path]
private lemma ODE_existsUnique_hasDerivAt_eq_continuousLinearMap_eq
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {B : ℝ → E →L[ℝ] E}
  {t₀ : ℝ}
  {x₀ : E}
-- given
  (hB : Continuous B) :
-- imply
  ∃! x : ℝ → E, x t₀ = x₀ ∧ ∀ t, HasDerivAt x (B t (x t)) t := by
-- proof
  apply ODE.existsUnique_hasDerivAt_eq_continuousLinearMap B t₀ x₀ hB

/--
[_root_.HasDerivAt.det_of_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/ODE/LinearSystemFundamentalMatrix.lean)
-/
@[path]
private lemma HasDerivAt_det_of_mul_eq
  {n : ℕ}
  {Φ : ℝ → Matrix (Fin n) (Fin n) ℝ}
  {A : Matrix (Fin n) (Fin n) ℝ}
  {t : ℝ}
-- given
  (hΦ : HasDerivAt Φ (A * Φ t) t) :
-- imply
  HasDerivAt (fun s ↦ (Φ s).det) (A.trace * (Φ t).det) t := by
-- proof
  apply HasDerivAt.det_of_mul hΦ

/--
[fundamental_matrix_linear_system](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/ODE/LinearSystemFundamentalMatrix.lean)
-/
@[path]
private lemma fundamental_matrix_linear_system_eq
  {n : ℕ}
  {A : ℝ → Matrix (Fin n) (Fin n) ℝ}
  {t₀ : ℝ}
-- given
  (hA : Continuous A) :
-- imply
  ∃ Φ : ℝ → Matrix (Fin n) (Fin n) ℝ, Φ t₀ = 1 ∧
    (∀ t, HasDerivAt Φ (A t * Φ t) t) ∧
    (∀ t, IsUnit (Φ t).det) ∧
    ∀ x₀ : Fin n → ℝ, ∃ x : ℝ → (Fin n → ℝ),
    x t₀ = x₀ ∧ (∀ t, HasDerivAt x ((A t).mulVec (x t)) t) ∧
    (∀ t, x t = (Φ t).mulVec x₀) ∧
    ∀ y : ℝ → (Fin n → ℝ), y t₀ = x₀ →
    (∀ t, HasDerivAt y ((A t).mulVec (y t)) t) → y = x := by
-- proof
  apply MathlibExt.Analysis.ODE.LinearSystemFundamentalMatrixWanted.fundamental_matrix_linear_system A t₀ hA

/--
[fundamental_matrix_liouville_det](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/ODE/LinearSystemFundamentalMatrix.lean)
-/
@[path]
private lemma fundamental_matrix_liouville_det_eq
  {n : ℕ}
  {A : ℝ → Matrix (Fin n) (Fin n) ℝ}
  {t₀ : ℝ}
  {Φ : ℝ → Matrix (Fin n) (Fin n) ℝ}
-- given
  (hA : Continuous A)
  (hΦ0 : Φ t₀ = 1)
  (hΦ : ∀ t, HasDerivAt Φ (A t * Φ t) t) :
-- imply
  ∀ t, (Φ t).det = (Φ t₀).det * Real.exp (∫ s in t₀..t, (A s).trace) := by
-- proof
  apply MathlibExt.Analysis.ODE.LinearSystemFundamentalMatrixWanted.fundamental_matrix_liouville_det A t₀ hA Φ hΦ0 hΦ


-- created on 2026-10-20
