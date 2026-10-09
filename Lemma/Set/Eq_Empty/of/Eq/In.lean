import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {α : Type*}
  [DecidableEq α]
  {A : Finset α}
  {a : α}
-- given
  (hcard : A.card = 1)
  (ha : a ∈ A) :
-- imply
  A.erase a = ∅ := by
-- proof
  obtain ⟨y, rfl⟩ := Finset.card_eq_one.mp hcard
  simp only [Finset.mem_singleton] at ha
  rw [ha, Finset.erase_singleton]


-- created on 2021-03-16
