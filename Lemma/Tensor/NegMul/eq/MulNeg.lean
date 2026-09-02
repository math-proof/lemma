import Lemma.Tensor.DataMul.eq.MulData
import Lemma.Tensor.DataMul.eq.MulDataS
import Lemma.Tensor.DataNeg.eq.NegData
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.NegMul.eq.MulNeg
open Tensor Vector


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.NegMul.eq.MulNeg |
| comm | Tensor.MulNeg.eq.NegMul |
| scalar | Tensor.NegMul.eq.MulNeg.scalar |
| comm.scalar | Tensor.MulNeg.eq.NegMul.scalar |
-/
@[main, comm]
private lemma main
  [Mul α] [HasDistribNeg α]
-- given
  (X Y : Tensor α s) :
-- imply
  -(X * Y) = -X * Y := by
-- proof
  apply Eq.of.EqDataS
  rw [DataNeg.eq.NegData]
  rw [DataMul.eq.MulDataS]
  rw [Vector.NegMul.eq.MulNeg]
  rw [DataMul.eq.MulDataS]
  rw [DataNeg.eq.NegData]


@[main, comm]
private lemma scalar
  [Mul α] [HasDistribNeg α]
-- given
  (X : Tensor α s)
  (a : α) :
-- imply
  -(X * a) = -X * a := by
-- proof
  apply Eq.of.EqDataS
  rw [DataNeg.eq.NegData]
  rw [DataMul.eq.MulData]
  rw [Vector.NegMul.eq.MulNeg.scalar]
  rw [DataMul.eq.MulData]
  rw [DataNeg.eq.NegData]


-- created on 2026-01-02
-- updated on 2026-09-02
