import Lemma.Nat.MulDiv.eq.Sub_Mod
import Lemma.Nat.Mul_Div.ge.SubAdd_1.of.Gt_0
import Lemma.Int.ToNatDiv.eq.DivToNat
import Lemma.Nat.CoeSub.eq.SubCoeS.of.Gt
import Lemma.Nat.Ceil.eq.DivAddSub_1
open Int Nat


@[main]
private lemma main
  {start stop step : ℕ}
-- given
  (h_start : start < stop)
  (h_step : step > 0) :
-- imply
  ⌈(stop - start : ℚ) / step⌉.toNat * step ∈ Ico (stop - start) (stop - start + step):= by
-- proof
  have h_ceil := Nat.Ceil.eq.DivAddSub_1 (stop - start) step (α := ℚ)
  rw [CoeSub.eq.SubCoeS.of.Gt h_start] at h_ceil
  rw [h_ceil, ToNatDiv.eq.DivToNat, MulDiv.eq.Sub_Mod]
  have hge := Nat.Mul_Div.ge.SubAdd_1.of.Gt_0 h_step (n := step - 1 + (stop - start)) (d := step)
  rw [Nat.mul_comm, MulDiv.eq.Sub_Mod] at hge
  grind


-- created on 2026-08-09
