import Lemma.Rat.EqMul.is.Eq_Div.of.Ne_0
import Lemma.Hyperreal.EqSt_0.is.Infinite.ou.Infinitesimal
import Lemma.Hyperreal.EqSt.of.InfinitesimalSub
import Lemma.Hyperreal.EqSt_0.of.Infinite
import Lemma.Hyperreal.EqSt_0.of.Infinitesimal
import Lemma.Hyperreal.Infinite.is.Infinite.of.Setoid
import Lemma.Hyperreal.Infinitesimal.is.Infinitesimal.of.Setoid
import Lemma.Hyperreal.Setoid.is.OrAndS
import Lemma.Hyperreal.StDiv.eq.DivStS.of.NotInfinite.NotInfinitesimal
open Hyperreal Rat


@[main, mt]
private lemma main
  {a b : ℝ*}
-- given
  (h : a ≈ b) :
-- imply
  a.st = b.st := by
-- proof
  if h_a : a.Infinitesimal then
    have h_b := Infinitesimal.of.Infinitesimal.Setoid h h_a
    have h_a := EqSt_0.of.Infinitesimal h_a
    have h_b := EqSt_0.of.Infinitesimal h_b
    aesop
  else if h_a_inf : a.Infinite then
    have h_b := Infinite.of.Infinite.Setoid h h_a_inf
    have h_a := EqSt_0.of.Infinite h_a_inf
    have h_b := EqSt_0.of.Infinite h_b
    aesop
  else
    have h' := h.symm
    have h_b := NotInfinitesimal.of.NotInfinitesimal.Setoid h' h_a
    have h := OrAndS.of.Setoid h
    simp [h_a, h_b] at h
    have h_st := EqSt.of.InfinitesimalSub h
    rw [StDiv.eq.DivStS.of.NotInfinite.NotInfinitesimal h_a_inf h_b] at h_st
    have h_b_inf := NotInfinite.of.NotInfinite.Setoid h' h_a_inf
    have h_st_b := NeSt_0.of.NotInfinite.NotInfinitesimal h_b_inf h_b
    have h_st := Eq_Mul.of.EqDiv.Ne_0 h_st_b h_st
    aesop


-- created on 2025-12-27
