import Theorem.Logic.SEq
import Def.Data.Tensor.Defs.Part4


@[path]
private lemma main
  {A : Tensor α s}
  {B : Tensor α s'}
-- given
  (h : A ≃ B)
  (i n : ℕ) :
-- imply
  A.data.array_slice i n ≃ B.data.array_slice i n := by
-- proof
  simp [SEq] at h ⊢
  let ⟨h_s, h⟩ := h
  let ⟨A_data⟩ := A
  let ⟨B_data⟩ := B
  aesop


-- created on 2025-06-29
-- updated on 2026-11-20
