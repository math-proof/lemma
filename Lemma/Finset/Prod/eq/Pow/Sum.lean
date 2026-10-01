import sympy.Basic


@[main]
private lemma main
  [CommMonoid α]
  {s : Finset ι}
  {a : α}
  {f : ι → ℕ} :
-- imply
  ∏ i ∈ s, a ^ f i = a ^ ∑ i ∈ s, f i :=
-- proof
  Finset.prod_pow_eq_pow_sum s f a


-- created on 2022-01-15
