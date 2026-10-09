import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {α : Type*}
  {A B : Set α}
-- given
  (h : A ∩ B = A ∪ B) :
-- imply
  A = B := by
-- proof
  have hAB : A ⊆ B := by
    intro z hz
    have : z ∈ A ∩ B := by
      rw [h]
      exact Or.inl hz
    exact this.2
  have hBA : B ⊆ A := by
    intro z hz
    have : z ∈ A ∩ B := by
      rw [h]
      exact Or.inr hz
    exact this.1
  exact Set.Subset.antisymm hAB hBA


-- created on 2021-04-03
