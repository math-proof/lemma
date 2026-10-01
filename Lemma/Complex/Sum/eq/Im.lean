import sympy.functions.elementary.complexes
import sympy.Basic
open Real


@[main]
private lemma main
  {n : ℕ}
  {z : ℕ → ℂ} :
-- imply
  ∑ k ∈ Finset.range n, im (z k) = im (∑ k ∈ Finset.range n, z k) := by
-- proof
  exact (Complex.im_sum _ _).symm


-- created on 2026-09-27
