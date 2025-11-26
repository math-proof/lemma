import sympy.tensor.Basic
import Lemma.Vector.HEq.of.EqValS
import Lemma.Bool.IffEqS.of.Eq
import Lemma.Tensor.Length.of.SEq
import Lemma.Bool.HEq.of.Cond.Cond
open Tensor Vector Bool


@[main]
private lemma main
  {A : Tensor α s}
  {B : Tensor α s'}
-- given
  (h_i : i < s.length)
  (h : A ≃ B)
  (g : (s : List ℕ) → Fin s.length → List ℕ)
  (f : (s : List ℕ) → (i : Fin s.length) → Tensor α s → Tensor α (g s i)) :
-- imply
  f s ⟨i, h_i⟩ A ≃ f s' ⟨i, by rwa [← h.left]⟩ B := by
-- proof
  simp [SEq] at h ⊢
  let ⟨h_s, h⟩ := h
  cases A
  cases B
  constructor
  ·
    simp_all
    congr
    simp_all
  ·
    congr
    aesop


@[main]
private lemma tensor
  {A : Tensor α s}
  {B : Tensor α s'}
-- given
  (h_i : i < A.length)
  (h : A ≃ B)
  (g : List ℕ → List ℕ)
  (f : (s : List ℕ) → (X : Tensor α s) → (i : Fin X.length) → Tensor α (g s)) :
-- imply
  f s A ⟨i, h_i⟩ ≃ f s' B ⟨i, by rwa [← Tensor.Length.of.SEq h]⟩ := by
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
    aesop


-- created on 2025-07-13
