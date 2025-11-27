import Lemma.Vector.EqGet0_0
open Vector


@[main]
private lemma main
  [GroupWithZero α]
-- given
  (n : ℕ) :
-- imply
  (0 : List.Vector α n)⁻¹ = 0 := by
-- proof
  simp [Inv.inv]
  ext i
  simp
  rw [EqGet0_0.fin]
  simp [inv_zero]


-- created on 2025-09-23
