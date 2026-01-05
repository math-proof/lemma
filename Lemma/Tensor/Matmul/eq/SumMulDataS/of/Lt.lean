import Lemma.List.Drop.eq.ListGet.of.GtLength_0
import Lemma.List.Drop.eq.ListGetS.of.GeLength_2
import Lemma.List.DropLast.eq.Take_SubLength_1
import Lemma.List.EqAppendS.of.Eq
import Lemma.List.EqAppendTake__Drop
import Lemma.List.EraseIdx.eq.Append_Drop_Add_1
import Lemma.List.EraseIdxAppend.eq.Append_EraseIdx.of.LeLength
import Lemma.Nat.EqAddMulDiv
import sympy.tensor.tensor
open Nat List


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (h : n < n')
  (X : Tensor α [n])
  (Y : Tensor α [n']) :
-- imply
  X.matmul Y =
    let q := n' / n
    let r := n' % n
    let X : Tensor α [n'] := cast
      (by simp [q, r, EqAddMulDiv])
      ((cast (by simp_all) (X.repeat q ⟨0, by simp⟩) : Tensor α [q * n]) ++ (0 : Tensor α [r]))
    ((X.data * Y.data).sum : Tensor α []) := by
-- proof
  unfold Tensor.matmul
  split_ifs
  repeat grind


-- created on 2026-01-05
