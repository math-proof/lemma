import Lemma.Int.Mul_Neg.eq.NegMul
import Lemma.Vector.GetMul.eq.MulGet
import Lemma.Vector.GetMul.eq.MulGetS
import Lemma.Vector.GetNeg.eq.NegGet
import sympy.vector.vector
open Int Vector


/--
| attributes | lemma |
| :---: | :---: |
| main | Vector.Mul_Neg.eq.NegMul |
| comm | Vector.NegMul.eq.Mul_Neg |
| scalar | Vector.Mul_Neg.eq.NegMul.scalar |
| comm.scalar | Vector.NegMul.eq.Mul_Neg.scalar |
-/
@[main, comm]
private lemma main
  [Mul α] [HasDistribNeg α]
-- given
  (x y : List.Vector α n) :
-- imply
  x * -y = -(x * y) := by
-- proof
  ext k
  rw [GetMul.eq.MulGetS.fin]
  rw [GetNeg.eq.NegGet.fin]
  rw [Int.Mul_Neg.eq.NegMul]
  rw [GetNeg.eq.NegGet.fin]
  rw [GetMul.eq.MulGetS.fin]


@[main, comm]
private lemma scalar
  [Mul α] [HasDistribNeg α]
-- given
  (x : List.Vector α n)
  (a : α) :
-- imply
  x * -a = -(x * a) := by
-- proof
  ext k
  rw [GetMul.eq.MulGet.fin]
  rw [Int.Mul_Neg.eq.NegMul]
  rw [GetNeg.eq.NegGet.fin]
  rw [GetMul.eq.MulGet.fin]


-- created on 2026-09-02
