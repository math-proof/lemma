import Lemma.Bool.SEqCast.of.Eq
import Lemma.List.EqAppendTake__ListGet.of.GeLength_2
import Lemma.List.EqAppendTake__ListGet.of.GtLength_0
import Lemma.Tensor.GetDot.as.DotGet.of.GtLengthS
import Lemma.Tensor.GetDot.eq.DotGet.of.Ne_Nil
import Lemma.Tensor.GtLengthDot.of.LeLengthS.Ne_Nil
import Lemma.Tensor.Length.of.SEq
import Lemma.Tensor.SEqDotS.of.SEq
import Lemma.Tensor.SEqGetS.of.SEq.GtLength
open Bool List Tensor


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
    let ys : List ℕ := n' :: s₀ :: s₁ :: tl
    have hXt := EqAppendTake__ListGet.of.GtLength_0 (show s.length > 0 by grind)
    let hX := congrArg (n :: ·) hXt
    let hY := EqAppendTake__ListGet.of.GeLength_2 (show ys.length ≥ 2 by grind)
    let X' := cast (congrArg (Tensor α) hX.symm) X
    let Y' := cast (congrArg (Tensor α) hY.symm) Y
    have h_get := GetDot.as.DotGet.of.GtLengthS (by grind) X' Y' i
    have hY_seq := (SEqCast.of.Eq hY.symm) Y
    have hX_seq := (SEqCast.of.Eq hX.symm) X
    have h_dotY := SEqDotS.of.SEq.left hY_seq X'
    have h_dotX := SEqDotS.of.SEq hX_seq Y
    have h_dot := SEq.trans h_dotY h_dotX
    have h_w := GtLengthDot.of.LeLengthS.Ne_Nil (by grind) (by omega) X Y i
    have h_lhs := SEqGetS.of.SEq.GtLength (by rwa [← Length.of.SEq h_dot] at h_w) h_dot
    have h_get_i := SEqGetS.of.SEq.GtLength i.isLt hX_seq
    have h_rhs := (SEqDotS.of.SEq.left hY_seq (X'[i])).trans (SEqDotS.of.SEq h_get_i Y)
    exact h_lhs.symm.trans (h_get.trans h_rhs)


-- created on 2026-01-04
-- updated on 2026-07-18
