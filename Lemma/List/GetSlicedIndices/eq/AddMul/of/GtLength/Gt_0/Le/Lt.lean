import Lemma.List.GetSlicedIndices.eq.AddMul.of.Lt.LeSubAddMul.Lt_SubAddMul
import Lemma.Nat.MulToNatCeilDivSub.in.Ico
open List Rat Int Nat Slice


@[main]
private lemma main
  {start stop step N i : ℕ}
-- given
  (h_start : start < stop)
  (h_stop : stop ≤ N)
  (h_step : step > 0)
  (h_i : i < (Nat.sliced_indices h_start h_stop h_step).length) :
-- imply
  (Nat.sliced_indices h_start h_stop h_step)[i] = start + i * step := by
-- proof
  have h_n := LengthSlicedIndices.eq.ToNatCeilDivSub.of.Gt_0.Le.Lt h_start h_stop h_step
  rw [h_n] at h_i
  have h_in := Nat.MulToNatCeilDivSub.in.Ico h_start h_step
  set n := ⌈(stop - start : ℚ) / step⌉.toNat
  set r := n * step + start - stop
  have h_stop_eq : stop = n * step + start - r := by grind
  rw [h_stop_eq] at h_start
  rw [h_stop_eq] at h_stop
  have := GetSlicedIndices.eq.AddMul.of.Lt.LeSubAddMul.Lt_SubAddMul (j := start) (d := step) (N := N) (n := n) (i := i) (j' := ⟨r, by grind⟩) h_start h_stop h_i
  grind


-- created on 2026-08-09
