import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [DecidableEq α]
  {X : Finset α}
  {a : ℕ → α}
  {x : α}
-- given
  (h : X = (Finset.range X.card).image a)
  (hx : x ∈ X) :
-- imply
  ∃ i < X.card, a i = x := by
-- proof
  try simp only [← Finset.mem_range] at *
  rw [h] at hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  exact ⟨i, hi, rfl⟩


-- created on 2021-03-22
