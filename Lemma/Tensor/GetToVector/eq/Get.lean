import Instance.Data.Tensor.Tensor
import Lemma.Tensor.Lt_HeadD
open Tensor


@[path, fin]
private lemma cons
-- given
  (X : Tensor α (n :: s))
  (i : Fin n) :
-- imply
  X.toVector[i] = X[i] := by
-- proof
  rfl

/--
| attributes | lemma |
| :---: | :---: |
| path | Tensor.GetToVector.eq.Get |
| fin | Tensor.GetToVector.eq.Get.fin |
-/
@[path, fin]
private lemma main
-- given
  (X : Tensor α s)
  (i : Fin X.length) :
-- imply
  X.toVector[i]'(Lt_HeadD i) = X[i] := by
-- proof
  have h_s := GtLength_0 i
  match s with
  | [] =>
    contradiction
  | s₀ :: s =>
    apply cons


-- created on 2025-05-23
-- updated on 2026-11-20
