import Lemma.Vector.GetMul.eq.MulGetS
import Lemma.Vector.GetMul.eq.MulGet
open Vector


@[main]
private lemma main
  [Mul α]
-- given
  (x : List.Vector α n)
  (a : α) :
-- imply
  x * a = x * List.Vector.replicate n a := by
-- proof
  ext i
  rw [GetMul.eq.MulGet.fin]
  simp [GetMul.eq.MulGetS.fin]


-- created on 2025-12-01
