import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.Eq_Stack
import sympy.tensor.functions
import sympy.tensor.stack
import Lemma.Vector.FlattenPow.eq.PowFlattenS
import Lemma.Vector.PowMapSRange.eq.MapFunPow
open Vector Tensor


@[main]
private lemma main
  [HPow α β α]
-- given
  (X : Tensor α (n :: s))
  (Y : Tensor β (n :: s)) :
-- imply
  [i < n] (X[i] ^ Y[i]) = X ^ Y := by
-- proof
  conv_rhs =>
    rw [Eq_Stack X]
    rw [Eq_Stack Y]
  apply Eq.symm
  unfold Stack Tensor.OfVector
  simp only [HPow.hPow]
  apply Eq.of.EqDataS
  simp [GetElem.getElem]
  simp [Tensor.map₂]
  let a := (List.Vector.range n).map fun x => (X.get x).data
  let b := (List.Vector.range n).map fun x => (Y.get x).data
  show a.flatten ^ b.flatten = ((List.Vector.range n).map fun x => (X.get x).data ^ (Y.get x).data).flatten
  rw [← FlattenPow.eq.PowFlattenS]
  congr
  exact PowMapSRange.eq.MapFunPow _ _


-- created on 2019-10-19
-- updated on 2026-08-24
