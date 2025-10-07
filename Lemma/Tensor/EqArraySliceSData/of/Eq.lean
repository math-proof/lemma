import stdlib.SEq
import sympy.tensor.Basic
import Lemma.Vector.HEq.of.EqValS
import Lemma.Bool.IffEqS.of.Eq
open Vector Bool


@[main]
private lemma main
  {A : Tensor α s}
  {B : Tensor α s'}
-- given
  (h : A ≃ B)
  (i : ℕ)
  (n : ℕ) :
-- imply
  A.data.array_slice i n ≃ B.data.array_slice i n := by
-- proof
  simp [SEq] at h ⊢
  let ⟨h_s, h⟩ := h
  let ⟨A_data⟩ := A
  let ⟨B_data⟩ := B
  aesop


-- created on 2025-06-29
