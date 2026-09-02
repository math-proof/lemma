import Lemma.Int.NegMul.eq.MulNeg
import Lemma.Vector.GetMul.eq.MulGet
import Lemma.Vector.GetMul.eq.MulGetS
import Lemma.Vector.GetNeg.eq.NegGet
import sympy.vector.vector
open Int Vector


/--
| attributes | lemma |
| :---: | :---: |
| main | Vector.NegMul.eq.MulNeg |
| comm | Vector.MulNeg.eq.NegMul |
| scalar | Vector.NegMul.eq.MulNeg.scalar |
| comm.scalar | Vector.MulNeg.eq.NegMul.scalar |
-/
@[main, comm]
private lemma main
  [Mul α] [HasDistribNeg α]
-- given
  (x y : List.Vector α n) :
-- imply
  -(x * y) = -x * y := by
-- proof
  ext k
  rw [GetNeg.eq.NegGet.fin]
  rw [GetMul.eq.MulGetS.fin]
  rw [Int.NegMul.eq.MulNeg]
  rw [GetMul.eq.MulGetS.fin]
  rw [GetNeg.eq.NegGet.fin]


@[main, comm]
private lemma scalar
  [Mul α] [HasDistribNeg α]
-- given
  (x : List.Vector α n)
  (a : α) :
-- imply
  -(x * a) = -x * a := by
-- proof
  ext k
  rw [GetNeg.eq.NegGet.fin]
  rw [GetMul.eq.MulGet.fin]
  rw [Int.NegMul.eq.MulNeg]
  rw [GetMul.eq.MulGet.fin]
  rw [GetNeg.eq.NegGet.fin]


-- created on 2026-01-02
-- updated on 2026-09-02
