import stdlib.SEq
import sympy.tensor.Basic
import Lemma.Vector.HEq.of.EqValS
import Lemma.Logic.IffEqS.of.Eq
open Logic Vector


@[main]
private lemma main
  {A : Tensor α s}
  {B : Tensor α s'}
-- given
  (h : A ≃ B)
  (g : List ℕ → List ℕ)
  (f : (s : List ℕ) → Tensor α s → Tensor α (g s)) :
-- imply
  f s A ≃ f s' B := by
-- proof
  simp [SEq] at h ⊢
  let ⟨h_s, h⟩ := h
  cases A
  cases B
  constructor
  ·
    simp_all
  ·
    congr


-- created on 2025-07-13
