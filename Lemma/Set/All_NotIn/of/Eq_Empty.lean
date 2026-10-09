import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {A B : Set α}
-- given
  (h : A ∩ B = ∅) :
-- imply
  ∀ x ∈ A, x ∉ B := by
-- proof
  intro x hx hxb
  have hm : x ∈ A ∩ B := ⟨hx, hxb⟩
  rw [h] at hm
  exact hm


-- created on 2021-05-12
