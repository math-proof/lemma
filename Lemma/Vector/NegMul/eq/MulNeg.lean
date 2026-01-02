import Lemma.Int.NegMul.eq.MulNeg
import Lemma.Vector.GetMul.eq.MulGet
import Lemma.Vector.GetNeg.eq.NegGet
import sympy.vector.vector
open Int Vector


@[main, comm]
private lemma main
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
  rw [NegMul.eq.MulNeg]
  rw [GetMul.eq.MulGet.fin]
  rw [GetNeg.eq.NegGet.fin]


-- created on 2026-01-02
