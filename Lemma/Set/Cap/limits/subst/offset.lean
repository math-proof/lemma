import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b k : ℤ}
  {f : ℤ → Set α} :
-- imply
  (⋂ i ∈ Finset.Ico a b, f i) = ⋂ i ∈ Finset.Ico (a + k) (b + k), f (i - k) := by
-- proof
  ext x
  simp only [Set.mem_iInter]
  refine ⟨?_, ?_⟩
  ·
    intro h i hi
    have hi' : i - k ∈ Finset.Ico a b := by
      rw [Finset.mem_Ico] at hi ⊢
      omega
    simpa using h (i - k) hi'
  ·
    intro h i hi
    have hi' : i + k ∈ Finset.Ico (a + k) (b + k) := by
      rw [Finset.mem_Ico] at hi ⊢
      omega
    simpa using h (i + k) hi'


-- created on 2026-10-11
-- updated on 2026-10-17
