import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {α : Type*}
  {A B C : Set α}
-- given
  (h : B ∩ C = ∅)
  (hs : A ⊆ B) :
-- imply
  C ∩ A = ∅ := by
-- proof
  ext x
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
  intro hx
  have : x ∈ B ∩ C := ⟨hs hx.2, hx.1⟩
  rw [h] at this
  exact this


-- created on 2021-05-14
