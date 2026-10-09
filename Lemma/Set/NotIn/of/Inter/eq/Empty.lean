import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a : ℤ}
  {B : Set ℤ}
-- given
  (h : {a} ∩ B = ∅) :
-- imply
  a ∉ B := by
-- proof
  intro ha
  have hm : a ∈ ({a} : Set ℤ) ∩ B := ⟨rfl, ha⟩
  rw [h] at hm
  exact hm


-- created on 2020-09-08
