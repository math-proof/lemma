import Lemma.Bool.SEq.is.Eq
import Lemma.List.EraseIdx.eq.Cons_EraseIdxTail.of.GtLength_0
import Lemma.List.EraseIdxTail.eq.TailEraseIdx.of.Lt_SubLength_1
import Lemma.Nat.Lt_Sub.of.LtAdd
import Lemma.Tensor.EqGet0_0
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.SEq.of.All_SEqGetS.Eq.GtLength_0
import Lemma.Tensor.SEq0S.of.Eq
import Lemma.Tensor.Sum.as.Stack_Sum.of.LtAdd_1Length
import Lemma.Tensor.Sum.eq.Zero.of.EqGet_0'0.of.GtLength_0
import sympy.tensor.tensor
open Bool List Nat Tensor


@[main]
private lemma main
  [Add α] [Zero α]
-- given
  (h_d : s.length > d)
  (h : s[d] = 0)
  (X : Tensor α s) :
-- imply
  X.sum d = 0 := by
-- proof
  induction d generalizing s X with
  | zero =>
    apply Sum.eq.Zero.of.EqGet_0'0.of.GtLength_0 h_d h
  | succ d ih =>
    apply Eq.of.SEq
    have := Sum.as.Stack_Sum.of.LtAdd_1Length h_d X
    apply this.trans
    apply SEq.of.All_SEqGetS.Eq.GtLength_0
    ·
      intro t
      rw [EqGet0_0.fin]
      rw [EqGetStack.fn.fin]
      have hi := Lt_Sub.of.LtAdd h_d
      rw [ih (by simpa) (by simpa)]
      apply SEq0S.of.Eq
      apply EraseIdxTail.eq.TailEraseIdx.of.Lt_SubLength_1 hi
    ·
      simp
    ·
      rw [EraseIdx.eq.Cons_EraseIdxTail.of.GtLength_0]


-- created on 2025-11-15
