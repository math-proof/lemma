import sympy.functions.elementary.complexes
import sympy.Basic
open Complex


@[main]
private lemma main
  {n : ℕ}
  {z : ℕ → ℂ} :
-- imply
  ∑ k ∈ Finset.range n, re (z k) = re (∑ k ∈ Finset.range n, z k) :=
-- proof
  (Complex.re_sum _ _).symm


-- created on 2023-06-03
