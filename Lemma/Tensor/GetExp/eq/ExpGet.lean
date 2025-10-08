import sympy.tensor.functions
import Lemma.Tensor.LengthExp.eq.Length
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.GetCast_Map.eq.UFnGet.of.Eq.Lt
import Lemma.List.ProdTake_1.eq.HeadD_1
import Lemma.Nat.Gt_0
import Lemma.Tensor.ProdTake_1.eq.Length.of.GtLength_0
import Lemma.Vector.GetUnflatten.eq.GetSplitAt_1
open Tensor Vector List Nat


@[main]
private lemma fin
  [Exp α]
-- given
  (X : Tensor α s)
  (i : Fin X.length) :
-- imply
  (exp X).get ⟨i, by simp [LengthExp.eq.Length]⟩ = exp (X.get i) := by
-- proof
  simp [Exp.exp]
  apply Eq.of.EqDataS
  simp [Tensor.get]
  simp [Tensor.toVector]
  rw [GetCast_Map.eq.UFnGet.of.Eq.Lt]
  ·
    simp [GetElem.getElem]
    rw [GetSplitAt_1.eq.GetUnflatten.fin]
    sorry
  ·
    have h_s := Gt_0 i
    simp [ProdTake_1.eq.Length.of.GtLength_0 h_s]
  ·
    apply ProdTake_1.eq.HeadD_1


@[main]
private lemma main
  [Exp α]
-- given
  (X : Tensor α s)
  (i : Fin X.length) :
-- imply
  have hi : i < (exp X).length := by simp [LengthExp.eq.Length]
  (exp X)[i] = exp X[i] := by
-- proof
  apply fin


-- created on 2025-10-08
