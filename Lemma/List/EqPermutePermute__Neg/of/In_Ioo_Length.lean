import sympy.sets.sets
import Lemma.Bool.IffEqS.of.Eq
import Lemma.List.GetPermute__Neg.eq.Ite.of.GtLength
import Lemma.List.GetPermute.eq.Ite.of.GtLength.GtLength
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
  (s.permute ⟨i, h.right⟩ (-d)).permute ⟨j, by simp [h_Ltj]⟩ d = s := by
-- proof
  let ⟨h_ij, h_j⟩ := h
  intro d h_Ltj
  ext k x
  if h_k_length : k < s.length then
    simp [h_k_length]
    apply IffEqS.of.Eq
    rw [GetPermute.eq.Ite.of.GtLength.GtLength (by simp; omega) (by simp; grind)]
    split_ifs <;>
    ·
      try simp
      rw [GetPermute__Neg.eq.Ite.of.GtLength]
      repeat grind
  else
    simp at h_k_length
    repeat rw [GetElem.eq.None.of.Ge_Length]
    repeat simpa


-- created on 2025-10-25
