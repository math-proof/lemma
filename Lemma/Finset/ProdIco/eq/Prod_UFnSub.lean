import sympy.Basic


@[main]
private lemma main
  [CommMonoid α]
-- given
  (c a b : ℤ)
  (f : ℤ → α) :
-- imply
  ∏ i ∈ Finset.Ico a b, f i = ∏ i ∈ Finset.Ico (c - b + 1) (c - a + 1), f (c - i) := by
-- proof
  apply Finset.prod_bij (fun i _ => c - i)
  ·
    intro i hi
    simp only [Finset.mem_Ico] at hi ⊢
    omega
  ·
    intro i _ j _ h
    omega
  ·
    intro j hj
    refine ⟨c - j, ?_, ?_⟩
    ·
      simp only [Finset.mem_Ico] at hj ⊢
      omega
    ·
      simp
  ·
    intro i hi
    simp


-- created on 2020-02-27
