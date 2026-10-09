import sympy.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic


@[path]
private lemma main
  {n : ℕ}
  {f : ℕ → ℕ → ℤ}
-- given
  (h : ∀ j i, f j i ≠ 0) :
-- imply
  Real.log (∏ j ∈ Finset.range n, ∏ i ∈ Finset.range n, (f j i : ℝ)) =
    ∑ j ∈ Finset.range n, ∑ i ∈ Finset.range n, Real.log (f j i) := by
-- proof
  rw [Real.log_prod fun j _ => Finset.prod_ne_zero_iff.mpr fun i _ => by exact_mod_cast h j i]
  exact Finset.sum_congr rfl fun j _ => Real.log_prod fun i _ => by exact_mod_cast h j i


-- created on 2019-12-11
