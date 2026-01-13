import Lemma.Bool.SEq.is.Eq
import Lemma.List.Eq.of.EqAppendS.EqLengthS
import sympy.tensor.Basic
open Bool List


@[main]
private lemma main
  {A : Tensor α (bz ++ n :: s)}
  {B : Tensor α (bz' ++ n' :: s')}
  {A' : Tensor α (bz ++ m :: s)}
  {B' : Tensor α (bz' ++ m' :: s')}
-- given
  (h_bz : bz.length = bz'.length)
  (h : A ≃ B)
  (h' : A' ≃ B') :
-- imply
  A ++ A' ≃ (B ++ B' : Tensor α _) := by
-- proof
  have h_s := h.left
  have h_s' := h'.left
  have h_bz' := Eq.of.EqAppendS.EqLengthS h_bz h_s
  have h_s := Eq.of.EqAppendS.EqLengthS.drop h_bz h_s
  have h_s' := Eq.of.EqAppendS.EqLengthS.drop h_bz h_s'
  injection h_s with h_n h_s_eq
  injection h_s' with h_n' h_s_eq
  subst h_n h_n' h_s_eq h_bz'
  have h := Eq.of.SEq h
  have h' := Eq.of.SEq h'
  rw [h, h']


-- created on 2026-01-13
