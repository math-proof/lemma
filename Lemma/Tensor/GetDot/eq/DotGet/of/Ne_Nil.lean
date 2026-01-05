import Lemma.List.Ne_Nil.is.GeLength_1
import Lemma.Tensor.GtLengthDot.of.LeLengthS.Ne_Nil
import stdlib.SEq
open List Tensor


@[main, fin]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (h_s : s ≠ [])
  (X : Tensor α (n :: s))
  (Y : Tensor α [n', k'])
  (i : Fin n) :
-- imply
  (X @ Y)[i]'(GtLengthDot.of.LeLengthS.Ne_Nil h_s (by apply GeLength_1.of.Ne_Nil h_s) X Y i) ≃ X[i] @ Y := by
-- proof
  simp [GetElem.getElem]
  induction s generalizing n' k' n with
  | nil =>
    contradiction
  | cons k ks ih =>
    match ks with
    | [] =>
      sorry
    | k' :: ks' =>
      sorry


-- created on 2026-01-04
