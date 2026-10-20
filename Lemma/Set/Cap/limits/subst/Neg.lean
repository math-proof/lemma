import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b : ℤ}
  {f : ℤ → Set α} :
-- imply
  (⋂ i ∈ Finset.Ico a b, f i) = ⋂ i ∈ Finset.Ico (1 - b) (1 - a), f (-i) := by
-- proof
  ext x
  simp only [Set.mem_iInter]
  refine ⟨?_, ?_⟩
  ·
    intro h i hi
    have hi' : -i ∈ Finset.Ico a b := by
      rw [Finset.mem_Ico] at hi ⊢
      omega
    simpa using h (-i) hi'
  ·
    intro h i hi
    have hi' : -i ∈ Finset.Ico (1 - b) (1 - a) := by
      rw [Finset.mem_Ico] at hi ⊢
      omega
    simpa using h (-i) hi'


-- created on 2021-01-28
-- updated on 2026-10-17
