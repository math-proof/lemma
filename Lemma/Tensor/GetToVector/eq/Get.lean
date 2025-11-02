import sympy.tensor.tensor
import Lemma.Tensor.Lt_HeadD
import Lemma.Tensor.GtLength_0
open Tensor


@[main]
private lemma cons
-- given
  (X : Tensor α (n :: s))
  (i : Fin n) :
-- imply
  X.toVector[i] = X[i] := by
-- proof
  simp [GetElem.getElem]
  simp [Tensor.get]
  simp [GetElem.getElem]


@[main]
private lemma cons.fin
-- given
  (X : Tensor α (n :: s))
  (i : Fin n) :
-- imply
  X.toVector.get i = X[i] := by
-- proof
  have := cons X i
  simp [GetElem.getElem] at *
  assumption


@[main]
private lemma fin
-- given
  (X : Tensor α s)
  (i : Fin X.length) :
-- imply
  X.toVector.get ⟨i, Lt_HeadD i⟩ = X.get i := by
-- proof
  have h_s := GtLength_0 i
  match s with
  | [] =>
    contradiction
  | s₀ :: s =>
    apply cons.fin


@[main]
private lemma main
-- given
  (X : Tensor α s)
  (i : Fin X.length) :
-- imply
  have := Lt_HeadD i
  X.toVector[i] = X[i] := by
-- proof
  apply fin


-- created on 2025-05-23
-- updated on 2025-10-06
