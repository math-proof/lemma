import Lemma.Nat.EqMul0_0
import Lemma.Vector.EqGet0_0
import Lemma.Vector.GetMul.eq.MulGet
import sympy.vector.vector
open Vector Nat


@[main]
private lemma main
  [MulZeroClass α]
-- given
  (n : ℕ)
  (a : α) :
-- imply
  (0 : List.Vector α n) * a = 0 := by
-- proof
  ext i
  rw [GetMul.eq.MulGet.fin]
  rw [EqGet0_0.fin]
  apply EqMul0_0


-- created on 2025-12-08
