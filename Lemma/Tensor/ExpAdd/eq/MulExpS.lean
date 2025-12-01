import Lemma.Tensor.DataAdd.eq.AddData
import Lemma.Tensor.DataAdd.eq.AddDataS
import Lemma.Tensor.DataExp.eq.ExpData
import Lemma.Tensor.DataMul.eq.MulData
import Lemma.Tensor.DataMul.eq.MulDataS
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.ExpAdd.eq.MulExpS
open Tensor Vector


@[main]
private lemma main
  [Exp α]
-- given
  (A B : Tensor α s) :
-- imply
  exp (A + B) = exp A * exp B := by
-- proof
  apply Eq.of.EqDataS
  simp [DataExp.eq.ExpData]
  simp [DataAdd.eq.AddDataS]
  simp [DataMul.eq.MulDataS]
  simp [ExpAdd.eq.MulExpS]
  simp [DataExp.eq.ExpData]


@[main]
private lemma scalar
  [Exp α]
-- given
  (X : Tensor α s)
  (a : α) :
-- imply
  exp (X + a) = exp X * exp a := by
-- proof
  apply Eq.of.EqDataS
  simp [DataExp.eq.ExpData]
  simp [DataAdd.eq.AddData]
  simp [DataMul.eq.MulData]
  simp [DataExp.eq.ExpData]
  simp [ExpAdd.eq.MulExpS.scalar]


-- created on 2025-12-01
