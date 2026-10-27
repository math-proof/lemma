import Mathlib
import Initialize.Tactic.Attr.Basic
open MeasureTheory ENNReal NNReal


/--
[holder_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/HolderInequality.lean)
-/
@[path]
lemma holder_inequality
  [MeasurableSpace α]
  {μ : Measure α}
  {p q : ℝ}
  {f g : α → ℝ}
-- given
  (hpq : p.HolderConjugate q)
  (hf : MemLp f (ENNReal.ofReal p) μ)
  (hg : MemLp g (ENNReal.ofReal q) μ) :
-- imply
  ∫ x, := by
-- proof
  have h1 : ∀ x, |f x * g x| = ‖f x‖ * ‖g x‖ := by
    intro x
    rw [abs_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  have h2 : ∀ x, |f x| ^ p = ‖f x‖ ^ p := by
    intro x
    rw [Real.norm_eq_abs]
  have h3 : ∀ x, |g x| ^ q = ‖g x‖ ^ q := by
    intro x
    rw [Real.norm_eq_abs]
  simp_rw [h1, h2, h3]
  exact integral_mul_norm_le_Lp_mul_Lq hpq hf hg


-- created on 2026-10-23
