import Lemma.Nat.Add
import Lemma.Real.Eq_1.of.Add_Inv.eq.Two
open Real Nat


@[main]
private lemma main
  {x : ℝ}
-- given
  (h : x⁻¹ + x = 2) :
-- imply
  x = 1 := by
-- proof
  rw [Add.comm] at h
  apply Eq_1.of.Add_Inv.eq.Two h


-- created on 2025-12-21
