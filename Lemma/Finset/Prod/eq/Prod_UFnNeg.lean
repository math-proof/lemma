import sympy.Basic


@[main]
private lemma main
  [CommMonoid α]
-- given
  (n : ℤ)
  (f : ℤ → α) :
-- imply
  ∏ i ∈ Finset.Ico (-n) (n + 1), f i = ∏ i ∈ Finset.Ico (-n) (n + 1), f (-i) := by
-- proof
  apply Finset.prod_bij (fun i _ => -i)
  ·
    intro i hi
    simp only [Finset.mem_Ico] at hi ⊢
    omega
  ·
    intro i _ j _ h
    apply neg_injective h
  ·
    intro j hj
    refine ⟨-j, ?_, ?_⟩
    ·
      simp only [Finset.mem_Ico] at hj ⊢
      omega
    ·
      simp
  ·
    intro i hi
    simp [neg_neg]


-- created on 2020-02-24
