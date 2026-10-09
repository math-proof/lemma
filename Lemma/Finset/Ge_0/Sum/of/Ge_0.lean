import sympy.Basic


@[path]
private lemma main
  {s : Finset ι}
  {h : ι → ℝ}
-- given
  (h₀ : ∀ k, h k ≥ 0) :
-- imply
  ∑ k ∈ s, h k ≥ 0 :=
-- proof
  Finset.sum_nonneg fun k _ => h₀ k


-- created on 2019-06-15
