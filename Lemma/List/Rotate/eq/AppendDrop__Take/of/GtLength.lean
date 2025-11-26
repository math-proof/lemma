import stdlib.List
import Lemma.Nat.EqMod.of.Lt
import Lemma.List.SplitAt.eq.MkTake__Drop
open List Nat


@[main]
private lemma main
  {s : List α}
  {n : ℕ}
-- given
  (h : s.length > n) :
-- imply
  s.rotate n = s.drop n ++ s.take n := by
-- proof
  unfold List.rotate
  rw [EqMod.of.Lt h]
  match h_v : s.splitAt n with
  | ⟨l₁, l₂⟩ =>
    simp
    rw [SplitAt.eq.MkTake__Drop] at h_v
    simp at h_v
    simp_all


-- created on 2025-06-15
-- updated on 2025-06-16
