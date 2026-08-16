import Lemma.List.LengthSlice.eq.SubMin
open List


@[main]
private lemma main
  {a b n : ℕ}
-- given
  (h_n : a < n)
  (h_b : a < b) :
-- imply
  (⟨a, b, 1⟩ : Slice).length n > 0 := by
-- proof
  rw [LengthSlice.eq.SubMin]
  apply Nat.sub_pos_of_lt
  exact lt_min_iff.mpr ⟨h_b, h_n⟩


-- created on 2026-08-16
