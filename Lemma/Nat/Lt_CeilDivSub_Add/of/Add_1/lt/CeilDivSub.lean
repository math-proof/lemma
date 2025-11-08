import Lemma.Int.Sub_Add.eq.SubSub
import Lemma.Rat.DivSub.eq.SubDivS
import Lemma.Bool.Ne.is.NotEq
import Lemma.Rat.Div.eq.One.of.Ne_0
import Lemma.Int.Lt_Sub.of.LtAdd
open Bool Int Rat


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]
  {start stop step i : ℕ}
-- given
  (h : i + 1 < ⌈(stop - start : α) / step⌉) :
-- imply
  i < ⌈(stop - (start + step) : α) / step⌉ := by
-- proof
  if h_step : step = 0 then
    rw [h_step] at h
    simp_all
    contradiction
  else
    have h_step := Ne.of.NotEq h_step
    have h_step : (step : α) ≠ 0 := by
      simp_all
    rw [Sub_Add.eq.SubSub]
    rw [DivSub.eq.SubDivS]
    simp [Div.eq.One.of.Ne_0 h_step]
    apply Lt_Sub.of.LtAdd h


-- created on 2025-05-24
