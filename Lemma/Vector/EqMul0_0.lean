import Lemma.Nat.EqMul0_0
import Lemma.Vector.EqGet0_0
import Lemma.Vector.GetMul.eq.MulGet
open Vector Nat


@[main, subst 0]
private lemma main
  [MulZeroClass α]
  {n : ℕ}
-- given
  (a : α) :
-- imply
  (0 : List.Vector α n) * a = 0 := by
-- proof
  ext i
  rw [GetMul.eq.MulGet.fin]
  rw [EqGet0_0.fin]
  apply EqMul0_0


-- created on 2025-12-08
