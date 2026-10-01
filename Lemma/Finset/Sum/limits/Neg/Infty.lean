import sympy.Basic


@[main]
private lemma main
  {f : ℤ → ℝ} :
-- imply
  ∑' i : ℤ, f i = ∑' i : ℤ, f (-i) :=
-- proof
  ((Equiv.neg ℤ).tsum_eq f).symm


-- created on 2020-03-16
