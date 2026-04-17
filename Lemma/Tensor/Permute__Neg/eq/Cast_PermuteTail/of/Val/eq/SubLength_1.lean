import Lemma.Tensor.Permute__Neg.as.PermuteTail.of.Val.eq.SubLength_1
import Lemma.Bool.SEq.is.EqCast.of.Eq
open Tensor Bool


@[main]
private lemma main
  {s : List ℕ}
  {i : Fin s.length}
-- given
  (h : i.val = s.length - 1)
  (X : Tensor α s)
  (d : ℕ) :
-- imply
  have h_s := List.Permute__Neg.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1 h d
  X.permute i (-d) = cast (congrArg (Tensor α) h_s.symm) (X.permuteTail (d + 1)) := by
-- proof
  intro h_s
  apply Eq_Cast.of.SEq.Eq
  .
    aesop
  .
    apply Permute__Neg.as.PermuteTail.of.Val.eq.SubLength_1 h


-- created on 2026-04-17
