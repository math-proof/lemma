import stdlib.List
import Lemma.Nat.EqMod.of.Lt
import Lemma.List.SplitAt.eq.MkTake__Drop
open List Nat


@[main]
private lemma main
  {v : List α}
  {n : ℕ}
-- given
  (h : n < v.length) :
-- imply
  v.rotate n = v.drop n ++ v.take n := by
-- proof
  unfold List.rotate
  rw [EqMod.of.Lt h]
  match h_v : v.splitAt n with
  | ⟨l₁, l₂⟩ =>
    simp
    rw [SplitAt.eq.MkTake__Drop] at h_v
    simp at h_v
    simp_all


-- created on 2025-06-15
-- updated on 2025-06-16
