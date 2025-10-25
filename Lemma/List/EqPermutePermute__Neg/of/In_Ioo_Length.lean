import sympy.sets.sets
import Lemma.Bool.IffEqS.of.Eq
import Lemma.List.LengthPermute.eq.Length
import Lemma.List.GetPermute__Neg.eq.Ite.of.Lt_Length
import Lemma.List.GetPermute.eq.Ite.of.Lt_Length.Lt_Length
import Lemma.List.GetElem.eq.None.of.Ge_Length
open Bool List


@[main]
private lemma main
  {s : List α}
-- given
  (h : i ∈ Ioo j s.length) :
-- imply
  let d := i - j
  have h_Ltj := h.left.trans h.right
  (s.permute ⟨i, h.right⟩ (-d)).permute ⟨j, by simp [LengthPermute.eq.Length, h_Ltj]⟩ d = s := by
-- proof
  let ⟨h_ij, h_j⟩ := h
  intro d h_Ltj
  ext k x
  by_cases h_k_length : k < s.length
  ·
    simp [h_k_length]
    have h_k : k < ((s.permute ⟨i, by linarith⟩ (-d)).permute ⟨j, by simp [LengthPermute.eq.Length, h_Ltj]⟩ d).length := by 
      simpa [LengthPermute.eq.Length]
    simp [h_k]
    apply IffEqS.of.Eq
    rw [GetPermute.eq.Ite.of.Lt_Length.Lt_Length (by simp [LengthPermute.eq.Length]; omega) (by simp [LengthPermute.eq.Length]; grind)]
    split_ifs <;>
    ·
      try simp
      rw [GetPermute__Neg.eq.Ite.of.Lt_Length]
      repeat grind
  ·
    simp at h_k_length
    repeat rw [GetElem.eq.None.of.Ge_Length]
    repeat simpa [LengthPermute.eq.Length]


-- created on 2025-10-25
