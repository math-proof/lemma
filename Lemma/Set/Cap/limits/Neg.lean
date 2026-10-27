import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {a : ℤ}
  {f : ℤ → Set α} :
-- imply
  (⋂ i ∈ Finset.Ico (-a) (a + 1), f i) = ⋂ i ∈ Finset.Ico (-a) (a + 1), f (-i) := by
-- proof
  ext x
  simp only [Set.mem_iInter]
  refine ⟨?_, ?_⟩
  ·
    intro h i hi
    have hneg : -i ∈ Finset.Ico (-a) (a + 1) := by
      rw [Finset.mem_Ico] at hi ⊢
      omega
    simpa using h (-i) hneg
  ·
    intro h i hi
    have hneg : -i ∈ Finset.Ico (-a) (a + 1) := by
      rw [Finset.mem_Ico] at hi ⊢
      omega
    simpa using h (-i) hneg


-- created on 2021-01-23
-- updated on 2026-10-26
