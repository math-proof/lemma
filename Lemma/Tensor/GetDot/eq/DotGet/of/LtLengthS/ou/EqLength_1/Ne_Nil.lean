import Lemma.List.Ne_Nil.is.GeLength_1
import Lemma.Tensor.GetDot.eq.DotGet.of.LtLengthS
import Lemma.Tensor.GetDot.eq.DotGet.of.Ne_Nil
import Lemma.Tensor.GtLengthDot.of.LeLengthS.Ne_Nil
open List Tensor


@[main, fin]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (h_s : s ≠ [])
  (h_len : s'.length < s.length ∨ s'.length = 1)
  (X : Tensor α (n :: s))
  (Y : Tensor α (n' :: s'))
  (i : Fin n) :
-- imply
  have h_len : s'.length ≤ s.length := by
    obtain h_len | h_len := h_len
    ·
      omega
    ·
      simp_all
      apply GeLength_1.of.Ne_Nil h_s
  (X @ Y)[i]'(GtLengthDot.of.LeLengthS.Ne_Nil h_s h_len X Y i) ≃ X[i] @ Y := by
-- proof
  obtain h_len | h_len := h_len
  ·
    apply GetDot.eq.DotGet.of.LtLengthS h_len
  ·
    match s' with
    | [k'] =>
      apply GetDot.eq.DotGet.of.Ne_Nil h_s


-- created on 2026-01-04
-- updated on 2026-01-05
