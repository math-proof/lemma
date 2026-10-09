import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import sympy.Basic


/--
Derivative of the softmax denominator:
\(\dfrac{d}{dt}\sum_i e^{g_i(t)}=\sum_i e^{g_i(t)}\,g_i'(t)\).
-/
@[path]
private lemma main
  {n : ℕ}
  {g : Fin n → ℝ → ℝ}
  {t : ℝ}
-- given
  (h : ∀ i, DifferentiableAt ℝ (g i) t) :
-- imply
  HasDerivAt (fun t => ∑ i, Real.exp (g i t)) (∑ i, Real.exp (g i t) * deriv (g i) t) t := by
-- proof
  apply HasDerivAt.fun_sum
  intro i _
  exact (h i).hasDerivAt.exp


-- created on 2026-10-01