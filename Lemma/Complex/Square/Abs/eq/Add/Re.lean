import sympy.functions.elementary.complexes
import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {a : ℕ → ℂ} :
-- imply
  ‖∑ i ∈ Finset.range n, a i‖ ^ 2 = ∑ i ∈ Finset.range n, ‖a i‖ ^ 2 + ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range i, 2 * (~(a i) * a j).re := by
-- proof
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Finset.sum_range_succ]
    have key : (~(a n) * ∑ j ∈ Finset.range n, a j).re = ∑ j ∈ Finset.range n, (~(a n) * a j).re := by
      rw [Finset.mul_sum, Complex.re_sum]
    rw [Complex.sq_norm, Complex.normSq_add, ← Complex.sq_norm, ← Complex.sq_norm, ih, ← Finset.mul_sum, ← key, mul_comm (∑ j ∈ Finset.range n, a j)]
    ring


-- created on 2023-06-24
