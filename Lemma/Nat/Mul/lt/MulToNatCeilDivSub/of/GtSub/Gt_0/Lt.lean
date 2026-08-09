import Lemma.Nat.MulToNatCeilDivSub.in.Ico
open Nat


@[main]
private lemma main
  {start stop step i : ℕ}
-- given
  (h_start : start < stop)
  (h_step : step > 0)
  (h : i * step < stop - start) :
-- imply
  i * step < ⌈((stop : ℚ) - start) / step⌉.toNat * step := by
-- proof
  have h_ico := Nat.MulToNatCeilDivSub.in.Ico h_start h_step
  rw [Set.mem_Ico] at h_ico
  obtain ⟨h_le, _⟩ := h_ico
  exact Nat.lt_of_lt_of_le h h_le


-- created on 2026-08-09
