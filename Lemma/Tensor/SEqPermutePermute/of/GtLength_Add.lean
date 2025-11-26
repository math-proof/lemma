import Lemma.Tensor.SEqPermute__0
import Lemma.Nat.Add
import Lemma.Nat.Le_Sub_1.of.Lt
import Lemma.Nat.Lt.is.Le.Ne
import Lemma.Tensor.SEqPermutePermute.of.Add.eq.SubLength_1
import Lemma.Tensor.SEqPermutePermute.of.Add.lt.SubLength_1
import Lemma.Tensor.SEqPermutePermute.of.EqSubLength_1
import Lemma.Tensor.SEqPermutePermute.of.LtSubLength_1
import Lemma.Tensor.SEqPermuteS.of.SEq.Eq.Eq.GtLength
open Nat Tensor


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h : s.length > i + d)
  (X : Tensor α s) :
-- imply
  (X.permute ⟨i, by linarith⟩ d).permute ⟨i + d, by simpa⟩ (-d) ≃ X := by
-- proof
  by_cases h_d : d = 0
  .
    subst h_d
    simp_all
    apply SEq.trans (SEqPermute__0 (X.permute ⟨i, by grind⟩ 0) ⟨i, by simp; omega⟩)
    apply SEqPermute__0
  .
    have : NeZero d := ⟨h_d⟩
    if h_i : i = 0 then
      subst h_i
      simp at h
      if h_d : d = s.length - 1 then
        have := SEqPermutePermute.of.EqSubLength_1 h_d X
        simp at this
        apply SEq.symm ∘ SEq.trans this.symm
        apply SEqPermuteS.of.SEq.Eq.Eq.GtLength
        repeat aesop
      else
        have h := Le_Sub_1.of.Lt h
        have h := Lt.of.Le.Ne h h_d
        have := SEqPermutePermute.of.LtSubLength_1 h X
        apply SEq.symm ∘ SEq.trans this.symm
        apply SEqPermuteS.of.SEq.Eq.Eq.GtLength
        repeat aesop
    else
      have : NeZero i := ⟨h_i⟩
      if h_d : i + d = s.length - 1 then
        apply SEqPermutePermute.of.Add.eq.SubLength_1 h_d
      else
        simp at h_i
        apply SEqPermutePermute.of.Add.lt.SubLength_1
        apply Lt.of.Le.Ne _ h_d
        apply Le_Sub_1.of.Lt h


-- created on 2025-10-19
-- updated on 2025-10-26
