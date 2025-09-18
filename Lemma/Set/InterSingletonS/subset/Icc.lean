import sympy.sets.sets
import Lemma.Basic


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


-- created on 2025-08-02
