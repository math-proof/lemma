import Lemma.Vector.GetMul.eq.MulGet
import Lemma.Vector.GetRepeat.eq.Get_Mod.of.Lt_Mul
open Vector


@[main]
private lemma main
  [Mul α]
-- given
  (x : List.Vector α n)
  (a : α)
  (d : ℕ) :
-- imply
  (x * a).repeat d = x.repeat d * a := by
-- proof
  ext i
  rw [GetMul.eq.MulGet.fin]
  repeat rw [GetRepeat.eq.Get_Mod.of.Lt_Mul.fin]
  rw [GetMul.eq.MulGet.fin]


-- created on 2025-12-01
