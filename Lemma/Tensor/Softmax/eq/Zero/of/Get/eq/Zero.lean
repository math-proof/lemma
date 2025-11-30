import Lemma.Bool.SEq.is.Eq
import Lemma.List.EqCons_Tail.of.GtLength_0
import Lemma.Nat.Lt_Sub.of.LtAdd
import Lemma.Tensor.EqGet0_0
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.SEq.of.All_SEqGetS.Eq.GtLength_0
import Lemma.Tensor.Softmax.as.Stack_Softmax.of.LtAdd_1Length
import Lemma.Tensor.Softmax.eq.Zero.of.EqGet_0'0.of.GtLength_0
open Bool Nat Tensor List


@[main]
private lemma main
  [ExpPos α]
-- given
  (h_d : s.length > d)
  (h : s[d] = 0)
  (X : Tensor α s) :
-- imply
  X.softmax d = 0 := by
-- proof
  induction d generalizing s X with
  | zero =>
    apply Softmax.eq.Zero.of.EqGet_0'0.of.GtLength_0 h_d h
  | succ d ih =>
    apply Eq.of.SEq
    have := Softmax.as.Stack_Softmax.of.LtAdd_1Length h_d X
    apply SEq.trans this
    apply SEq.of.All_SEqGetS.Eq.GtLength_0
    ·
      intro t
      rw [EqGet0_0.fin]
      rw [EqGetStack.fn.fin]
      have hi := Lt_Sub.of.LtAdd h_d
      rw [ih (by simpa) (by simpa)]
    ·
      simp
    ·
      apply EqCons_Tail.of.GtLength_0


-- created on 2025-11-30
