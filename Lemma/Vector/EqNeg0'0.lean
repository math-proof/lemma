import Lemma.Int.EqNeg0'0
import sympy.vector.vector
open Vector Int


@[path]
private lemma main
  [AddGroupWithOne α]
  {n : ℕ} :
-- imply
  -((0 : ℕ) : List.Vector α n) = 0 := by
-- proof
  rw [Nat.cast_zero]
  ext i
  rw [GetNeg.eq.NegGet.fin]
  rw [EqGet0_0.fin]
  apply EqNeg0'0


-- created on 2026-09-04
