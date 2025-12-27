import Lemma.Hyperreal.Ne_0.of.NotInfinitesimal
import Lemma.Hyperreal.Infinite.is.InfinitePos.ou.InfiniteNeg
import Lemma.Hyperreal.EqSt.of.InfinitesimalSub
import Lemma.Hyperreal.InfiniteDiv.of.Infinite.NotInfinite
import Lemma.Hyperreal.InfiniteNeg.is.InfinitesimalExp
import Lemma.Hyperreal.InfinitesimalSub.of.EqSt.NotInfinite
import Lemma.Hyperreal.LeSt_0.of.Le_0
import Lemma.Hyperreal.NotInfinite.of.Infinitesimal
import Lemma.Hyperreal.Setoid.is.OrAndS
import Lemma.Rat.Gt0Div.of.Lt_0.Gt_0
import sympy.functions.elementary.exponential
open Hyperreal Rat


@[main]
private lemma main
  {a b : ℝ*}
-- given
  (h : a ≈ b) :
-- imply
  a.exp ≈ b.exp := by
-- proof
  have := Hyperreal.exp_eq_exp (x := a) (y := b)
  apply Setoid.of.OrAndS
  if h_a : a.InfiniteNeg then
    have h_a_exp := InfinitesimalExp.of.InfiniteNeg h_a
    simp [h_a_exp]
    have h := OrAndS.of.Setoid h
    have ⟨h_a, h_a_lt_0⟩ := Infinite.Lt_0.of.InfiniteNeg h_a
    simp [NotInfinitesimal.of.Infinite h_a] at h
    have ⟨h, h_b_eps⟩ := h
    have h_st := EqSt.of.InfinitesimalSub h
    if h_b_neg : b.InfiniteNeg then
      have h_b_exp := InfinitesimalExp.of.InfiniteNeg h_b_neg
      simp [h_b_exp]
    else if h_b_pos : b.InfinitePos then
      have ⟨h_b, h_b_lt_0⟩ := Infinite.Gt_0.of.InfinitePos h_b_pos
      have h_ab := Gt0Div.of.Lt_0.Gt_0 h_a_lt_0 h_b_lt_0
      have h_ab_st := LeSt_0.of.Le_0 (by linarith) (x := a / b)
      linarith
    else
      have h_b_inf := NotInfinite.of.NotInfinitePos.NotInfiniteNeg ⟨h_b_pos, h_b_neg⟩
      have : NeZero b := ⟨Ne_0.of.NotInfinitesimal h_b_eps⟩
      have := InfiniteDiv.of.Infinite.NotInfinite h_a h_b_inf
      have := EqSt_0.of.Infinite this
      linarith
  else
    sorry


-- created on 2025-12-24
-- updated on 2025-12-26
