import Lemma.Vector.GetMul.eq.MulGetS
import Lemma.Vector.GetRepeat.eq.Get_Mod.of.Lt_Mul
open Vector


@[main]
private lemma main
  [Mul α]
-- given
  (x y : List.Vector α n)
  (d : ℕ) :
-- imply
  (x * y).repeat d = x.repeat d * y.repeat d := by
-- proof
  ext i
  rw [GetMul.eq.MulGetS.fin]
  repeat rw [GetRepeat.eq.Get_Mod.of.Lt_Mul.fin]
  rw [GetMul.eq.MulGetS.fin]


-- created on 2025-12-04
