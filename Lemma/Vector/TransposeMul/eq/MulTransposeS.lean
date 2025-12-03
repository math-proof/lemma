import Lemma.Vector.GetMul.eq.MulGetS
import Lemma.Vector.GetTranspose.eq.Get
import sympy.vector.vector
open Vector


@[main, comm]
private lemma main
  [Mul α]
-- given
  (a b : List.Vector (List.Vector α n) m) :
-- imply
  (a * b).transpose = a.transpose * b.transpose := by
-- proof
  ext i j
  simp [GetMul.eq.MulGetS.fin]
  simp [GetTranspose.eq.Get.fin]
  simp [GetMul.eq.MulGetS.fin]


-- created on 2025-12-03
