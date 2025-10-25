import Lemma.Int.Sub_Add.eq.SubSub
import Lemma.Rat.DivSub.eq.SubDivS
import Lemma.Bool.Ne.is.NotEq
import Lemma.Rat.Div.eq.One.of.Ne_0
import Lemma.Int.Lt_Sub.of.LtAdd
open Bool Int Rat


@[main]
private lemma main
  {start stop step i : ℕ}
-- given
  (h : i + 1 < ⌈(stop - start : ℚ) / step⌉) :
-- imply
  i < ⌈(stop - (start + step) : ℚ) / step⌉ := by
-- proof
  by_cases h_step : step = 0
  ·
    rw [h_step] at h
    simp_all
    contradiction
  ·
    have h_step := Ne.of.NotEq h_step
    have h_step : (step : ℚ) ≠ 0 := by
      simp_all
    rw [Sub_Add.eq.SubSub]
    rw [DivSub.eq.SubDivS]
    simp [Div.eq.One.of.Ne_0 h_step]
    apply Lt_Sub.of.LtAdd h


-- created on 2025-05-24
