import Lemma.Bool.SEq.is.Eq
import sympy.tensor.Basic
open Bool


@[main]
private lemma main
  {A : Tensor α (n :: s)}
  {B : Tensor α (m :: s')}
  {A' : Tensor α (n' :: s)}
  {B' : Tensor α (m' :: s')}
-- given
  (h : A ≃ B)
  (h' : A' ≃ B') :
-- imply
  A ++ A' ≃ B ++ B' := by
-- proof
  have h_s := h.left
  have h_s' := h'.left
  injection h_s with h_n h_s_eq
  injection h_s' with h_n' h_s_eq
  subst h_n h_n' h_s_eq
  have h := Eq.of.SEq h
  have h' := Eq.of.SEq h'
  rw [h, h']


-- created on 2026-01-13
