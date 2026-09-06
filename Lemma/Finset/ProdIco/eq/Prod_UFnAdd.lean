import sympy.Basic


@[main]
private lemma main
  [CommMonoid α]
-- given
  (a b d : ℤ)
  (f : ℤ → α) :
-- imply
  ∏ n ∈ Finset.Ico a b, f n = ∏ n ∈ Finset.Ico (a - d) (b - d), f (n + d) := by
-- proof
  apply Finset.prod_bij (fun m _ => m - d)
  ·
    intro m hm
    simp only [Finset.mem_Ico] at hm ⊢
    omega
  ·
    intro m₁ _ m₂ _ h
    omega
  ·
    intro n hn
    refine ⟨n + d, ?_, ?_⟩
    ·
      simp only [Finset.mem_Ico] at hn ⊢
      omega
    ·
      simp
  ·
    intro m hm
    simp


-- created on 2020-02-26
