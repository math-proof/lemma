import sympy.sets.sets
import Lemma.Bool.IffEqS.of.Eq
import Lemma.List.GetPermute__Neg.eq.Ite.of.Lt_Length
import Lemma.List.GetPermute.eq.Ite.of.Lt_Length.Lt_Length
import Lemma.List.GetElem.eq.None.of.Ge_Length
open Bool List


@[main]
private lemma main
  {s : List α}
-- given
  (h : j ∈ Ioo i s.length) :
-- imply
  let d := j - i
  (s.permute ⟨i, h.left.trans h.right⟩ d).permute ⟨j, by simp [h.right]⟩ (-d) = s := by
-- proof
  let ⟨h_ij, h_j⟩ := h
  intro d
  ext k x
  if h_k_length : k < s.length then
    simp [h_k_length]
    apply IffEqS.of.Eq
    rw [GetPermute__Neg.eq.Ite.of.Lt_Length (by simpa)]
    split_ifs <;>
    ·
      try simp
      rw [GetPermute.eq.Ite.of.Lt_Length.Lt_Length]
      repeat grind
  else
    simp at h_k_length
    repeat rw [GetElem.eq.None.of.Ge_Length]
    repeat simpa


-- created on 2025-10-12
-- updated on 2025-10-25
