import Lemma.List.LengthPermute.eq.Length
import Lemma.Nat.Add
import Lemma.Nat.Le_Sub_1.of.Lt
import Lemma.Nat.Lt.of.Le.Ne
import Lemma.Tensor.SEqPermutePermute.of.Add.lt.SubLength_1
import Lemma.Tensor.SEqPermutePermute.of.EqSubLength_1
import Lemma.Tensor.SEqPermuteS.of.SEq.Eq.Eq.Lt_Length
import Lemma.Tensor.SEqPermutePermute.of.LtSubLength_1
import Lemma.Tensor.SEqPermutePermute.of.Add.eq.SubLength_1
open List Nat Tensor


@[main]
private lemma main
  [NeZero (d : ℕ)]
  {s : List ℕ}
-- given
  (h : s.length > i + d)
  (X : Tensor α s) :
-- imply
  (X.permute ⟨i, by linarith⟩ d).permute ⟨i + d, by simpa [LengthPermute.eq.Length]⟩ (-d) ≃ X := by
-- proof
  by_cases h_i : i = 0
  ·
    subst h_i
    simp at h
    by_cases h_d : d = s.length - 1
    ·
      have := SEqPermutePermute.of.EqSubLength_1 h_d X
      simp at this
      apply SEq.symm ∘ SEq.trans this.symm
      apply SEqPermuteS.of.SEq.Eq.Eq.Lt_Length
      repeat aesop
    ·
      have h := Le_Sub_1.of.Lt h
      have h := Lt.of.Le.Ne h_d h
      have := SEqPermutePermute.of.LtSubLength_1 h X
      apply SEq.symm ∘ SEq.trans this.symm
      apply SEqPermuteS.of.SEq.Eq.Eq.Lt_Length
      repeat aesop
  ·
    have : NeZero i := ⟨h_i⟩
    by_cases h_d : i + d = s.length - 1
    ·
      apply SEqPermutePermute.of.Add.eq.SubLength_1 h_d
    ·
      simp at h_i
      apply SEqPermutePermute.of.Add.lt.SubLength_1
      apply Lt.of.Le.Ne h_d
      apply Le_Sub_1.of.Lt h


@[main]
private lemma reverse
  [NeZero (d : ℕ)]
  {s : List ℕ}
-- given
  (h : s.length > i + d)
  (X : Tensor α s) :
-- imply
  (X.permute ⟨i + d, by linarith⟩ (-d)).permute ⟨i, by simp [LengthPermute.eq.Length]; omega⟩ d ≃ X := by
-- proof
  by_cases h_i : i = 0
  ·
    subst h_i
    simp at h
    by_cases h_d : d = s.length - 1
    ·
      have := SEqPermutePermute.of.EqSubLength_1.reverse h_d X
      simp at this
      apply SEq.symm ∘ SEq.trans this.symm
      apply SEqPermuteS.of.SEq.Eq.Eq.Lt_Length
      repeat omega
      apply SEqPermuteS.of.SEq.Eq.Eq.Lt_Length _ _ (by rfl) (by rfl)
      simp
    ·
      have h := Le_Sub_1.of.Lt h
      have h := Lt.of.Le.Ne h_d h
      have := SEqPermutePermute.of.LtSubLength_1.reverse h X
      apply SEq.symm ∘ SEq.trans this.symm
      apply SEqPermuteS.of.SEq.Eq.Eq.Lt_Length
      repeat rfl
      apply SEqPermuteS.of.SEq.Eq.Eq.Lt_Length _ _ (by rfl) (by rfl)
      simp
  ·
    have : NeZero i := ⟨h_i⟩
    by_cases h_d : i + d = s.length - 1
    ·
      apply SEqPermutePermute.of.Add.eq.SubLength_1.reverse h_d
    ·
      simp at h_i
      apply SEqPermutePermute.of.Add.lt.SubLength_1.reverse
      apply Lt.of.Le.Ne h_d
      apply Le_Sub_1.of.Lt h


-- created on 2025-10-19
