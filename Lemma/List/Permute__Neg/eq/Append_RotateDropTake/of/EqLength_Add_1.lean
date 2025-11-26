import Lemma.List.EqTake.of.LeLength
import Lemma.List.TakePermute__Neg.eq.Append_RotateDropTake
open List


@[main, comm]
private lemma main
  {s : List α}
  {i d : ℕ}
-- given
  (h : s.length = i + d + 1) :
-- imply
  s.permute ⟨i + d, by grind⟩ (-d) = s.take i ++ (s.drop i).rotate d := by
-- proof
  have := TakePermute__Neg.eq.Append_RotateDropTake (s := s) ⟨i + d, by grind⟩ d
  simp at this
  simp [← h] at this
  rw [← this]
  rw [EqTake.of.LeLength]
  simp


-- created on 2025-10-27
