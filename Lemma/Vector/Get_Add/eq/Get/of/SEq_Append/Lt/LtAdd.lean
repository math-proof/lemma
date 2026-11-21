import Lemma.Vector.Get_Add.eq.Get.of.Val.eq.ValAppend.Lt.LtAdd
import Lemma.Vector.Val.of.SEq
open Vector


@[path]
private lemma main
  {a : List.Vector α N}
  {b : List.Vector α m}
  {c : List.Vector α n}
-- given
  (h₀ : m + i < N)
  (h₁ : i < n)
  (h₂ : a ≃ b ++ c) :
-- imply
  getElem a (m + i) h₀ = getElem c i h₁ := by
-- proof
  apply Get_Add.eq.Get.of.Val.eq.ValAppend.Lt.LtAdd h₀ h₁
  apply Val.of.SEq h₂


-- created on 2025-06-04
-- updated on 2026-11-20
