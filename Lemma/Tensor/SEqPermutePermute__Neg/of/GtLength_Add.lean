import Lemma.Nat.Add
import Lemma.Nat.Le_Sub_1.of.Lt
import Lemma.Nat.Lt.of.Le.Ne
import Lemma.Tensor.SEqPermutePermute__Neg.of.Add.eq.SubLength_1
import Lemma.Tensor.SEqPermutePermute__Neg.of.Add.lt.SubLength_1
import Lemma.Tensor.SEqPermutePermute__Neg.of.EqSubLength_1
import Lemma.Tensor.SEqPermutePermute__Neg.of.LtSubLength_1
import Lemma.Tensor.SEqPermuteS.of.SEq.Eq.Eq.Lt_Length
open Nat Tensor


@[main]
private lemma main
  [NeZero (d : ℕ)]
  {s : List ℕ}
-- given
  (h : s.length > i + d)
  (X : Tensor α s) :
-- imply
  (X.permute ⟨i + d, by linarith⟩ (-d)).permute ⟨i, by simp; omega⟩ d ≃ X := by
-- proof
  by_cases h_i : i = 0
  ·
    subst h_i
    simp at h
    by_cases h_d : d = s.length - 1
    ·
      have := SEqPermutePermute__Neg.of.EqSubLength_1 h_d X
      simp at this
      apply SEq.symm ∘ SEq.trans this.symm
      apply SEqPermuteS.of.SEq.Eq.Eq.Lt_Length
      repeat omega
      apply SEqPermuteS.of.SEq.Eq.Eq.Lt_Length _ _ (by rfl) (by rfl)
      simp
    ·
      have h := Le_Sub_1.of.Lt h
      have h := Lt.of.Le.Ne h_d h
      have := SEqPermutePermute__Neg.of.LtSubLength_1 h X
      apply SEq.symm ∘ SEq.trans this.symm
      apply SEqPermuteS.of.SEq.Eq.Eq.Lt_Length
      repeat rfl
      apply SEqPermuteS.of.SEq.Eq.Eq.Lt_Length _ _ (by rfl) (by rfl)
      simp
  ·
    have : NeZero i := ⟨h_i⟩
    by_cases h_d : i + d = s.length - 1
    ·
      apply SEqPermutePermute__Neg.of.Add.eq.SubLength_1 h_d
    ·
      simp at h_i
      apply SEqPermutePermute__Neg.of.Add.lt.SubLength_1
      apply Lt.of.Le.Ne h_d
      apply Le_Sub_1.of.Lt h


-- created on 2025-10-26
