import sympy.tensor.tensor
import Lemma.Tensor.Lt_HeadD
import Lemma.Tensor.GtLength_0
open Tensor


@[main]
private lemma main
-- given
  (v : Tensor α (n :: s))
  (i : Fin n) :
-- imply
  v.toVector[i] = v[i] := by
-- proof
  simp [GetElem.getElem]
  simp [Tensor.get]
  simp [GetElem.getElem]


@[main]
private lemma fin
-- given
  (v : Tensor α (n :: s))
  (i : Fin n) :
-- imply
  v.toVector.get i = v[i] := by
-- proof
  have := main v i
  simp [GetElem.getElem] at *
  assumption


@[main]
private nonrec lemma length.fin
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
    apply fin


@[main]
private lemma length
-- given
  (X : Tensor α s)
  (i : Fin X.length) :
-- imply
  have := Lt_HeadD i
  X.toVector[i] = X[i] := by
-- proof
  apply length.fin


-- created on 2025-05-23
-- updated on 2025-10-06
