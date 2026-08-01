import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  [Preorder α]
-- given
  (x y : α) :
-- imply
  {x} ∩ {y} ⊆ Icc x y := by
-- proof
  intro z hz
  simp at hz
  obtain ⟨rfl, rfl⟩ := hz
  exact ⟨by rfl, by rfl⟩


-- created on 2018-09-11
