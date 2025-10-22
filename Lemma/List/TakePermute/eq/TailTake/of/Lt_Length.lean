import Lemma.List.TakePermute.eq.RotateTake.of.Lt_Length
import Lemma.List.TakeTake.eq.Take.of.Ge
import Lemma.List.Rotate.eq.AppendDrop__Take.of.Le_Length
import Lemma.List.EqTakeAppend.of.Eq_Length
open List


@[main]
private lemma main
  {s : List α}
-- given
  (h : d < s.length) :
-- imply
  (s.permute ⟨0, by grind⟩ d).take d = (s.take (d + 1)).tail := by
-- proof
  have h_take := TakePermute.eq.RotateTake.of.Lt_Length h
  have h_take := congrArg (·.take d) h_take
  simp [TakeTake.eq.Take.of.Ge] at h_take
  rw [h_take]
  rw [Rotate.eq.AppendDrop__Take.of.Le_Length (by grind)]
  rw [EqTakeAppend.of.Eq_Length (by grind)]
  simp


-- created on 2025-10-22
