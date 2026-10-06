import sympy.Basic


@[main]
private lemma main
  {i n : ℤ}
  {f : ℤ → Set α}
-- given
  (h : i ≤ n) :
-- imply
  (⋂ k ∈ Finset.Ico i n, f k) ∩ f n = ⋂ k ∈ Finset.Ico i (n + 1), f k := by
-- proof
  have e : Finset.Ico i (n + 1) = insert n (Finset.Ico i n) := by
    ext k
    simp only [Finset.mem_Ico, Finset.mem_insert]
    omega
  rw [e, Finset.set_biInter_insert, Set.inter_comm]


-- created on 2021-07-12
