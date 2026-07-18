import Lemma.List.Ne_Nil.is.GeLength_1
import Lemma.Tensor.GetDot.eq.DotGet.of.Ne_Nil
import Lemma.Tensor.GtLengthDot.of.LeLengthS.Ne_Nil
open List Tensor
set_option maxHeartbeats 1000000


@[main, fin]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (h_len : s.length > s'.length)
  (X : Tensor α (n :: s))
  (Y : Tensor α (n' :: s'))
  (i : Fin n) :
-- imply
  (X @ Y)[i]'(GtLengthDot.of.LeLengthS.Ne_Nil (by grind) (by omega) X Y i) ≃ X[i] @ Y := by
-- proof
  have h_s : s ≠ [] := by grind
  match s' with
  | [] =>
    apply GetDot.eq.DotGet.of.Ne_Nil.une h_s
  | [k'] =>
    apply GetDot.eq.DotGet.of.Ne_Nil h_s
  | s₀ :: s₁ :: tl =>
    sorry


-- created on 2026-01-04
-- updated on 2026-07-15
