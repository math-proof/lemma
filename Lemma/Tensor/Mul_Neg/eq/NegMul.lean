import Lemma.Tensor.DataMul.eq.MulData
import Lemma.Tensor.DataMul.eq.MulDataS
import Lemma.Tensor.DataNeg.eq.NegData
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.Mul_Neg.eq.NegMul
open Tensor Vector


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.Mul_Neg.eq.NegMul |
| comm | Tensor.NegMul.eq.Mul_Neg |
| scalar | Tensor.Mul_Neg.eq.NegMul.scalar |
| comm.scalar | Tensor.NegMul.eq.Mul_Neg.scalar |
-/
@[main, comm]
private lemma main
  [Mul α] [HasDistribNeg α]
-- given
  (X Y : Tensor α s) :
-- imply
  X * -Y = -(X * Y) := by
-- proof
  apply Eq.of.EqDataS
  rw [DataMul.eq.MulDataS]
  rw [DataNeg.eq.NegData]
  rw [Vector.Mul_Neg.eq.NegMul]
  rw [DataNeg.eq.NegData]
  rw [DataMul.eq.MulDataS]


@[main, comm]
private lemma scalar
  [Mul α] [HasDistribNeg α]
-- given
  (X : Tensor α s)
  (a : α) :
-- imply
  X * -a = -(X * a) := by
-- proof
  apply Eq.of.EqDataS
  rw [DataMul.eq.MulData]
  rw [Vector.Mul_Neg.eq.NegMul.scalar]
  rw [DataNeg.eq.NegData]
  rw [DataMul.eq.MulData]


-- created on 2026-09-02
