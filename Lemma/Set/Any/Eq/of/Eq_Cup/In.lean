import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  [DecidableEq α]
  {X : Finset α}
  {a : ℕ → α}
  {x : α}
-- given
  (h : X = (Finset.range X.card).image a)
  (hx : x ∈ X) :
-- imply
  ∃ i ∈ Finset.range X.card, a i = x := by
-- proof
  rw [h] at hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  exact ⟨i, hi, rfl⟩


-- created on 2021-03-22
