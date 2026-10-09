import sympy.Basic


@[path]
private lemma main
  [CommMonoid α]
  [Add α]
  {n : ℕ}
  {f h : ℕ → α} :
-- imply
  ∏ k ∈ Finset.Ico 0 (n + 1), (f k + h k) = (f 0 + h 0) * ∏ k ∈ Finset.Ico 1 (n + 1), (f k + h k) :=
-- proof
  Finset.prod_eq_prod_Ico_succ_bot (Nat.zero_lt_succ n) (fun k => f k + h k)


-- created on 2023-03-22
-- updated on 2023-04-03
