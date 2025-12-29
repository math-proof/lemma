import Lemma.Hyperreal.Infinite.is.InfinitePos.ou.InfiniteNeg
import Lemma.Hyperreal.EqSt.of.InfinitesimalSub
import Lemma.Hyperreal.EqSt_0.of.Infinite
import Lemma.Hyperreal.EqSt_0.of.Infinitesimal
import Lemma.Hyperreal.InfiniteDiv.of.Infinite.NotInfinite
import Lemma.Hyperreal.InfiniteNeg.is.InfiniteNeg.of.Setoid
import Lemma.Hyperreal.InfiniteNeg.is.InfinitesimalExp
import Lemma.Hyperreal.InfinitePos.is.InfiniteExp
import Lemma.Hyperreal.InfinitePos.is.InfinitePos.of.Setoid
import Lemma.Hyperreal.InfinitesimalSub.of.EqSt.NotInfinite
import Lemma.Hyperreal.LeSt_0.of.Le_0
import Lemma.Hyperreal.Ne_0.of.NotInfinitesimal
import Lemma.Hyperreal.NotInfinite.of.Infinitesimal
import Lemma.Hyperreal.NotInfinitePos.of.Infinitesimal
import Lemma.Hyperreal.Setoid.is.OrAndS
import Lemma.Hyperreal.Setoid.of.InfinitesimalSub
import Lemma.Hyperreal.StExp.eq.ExpSt.of.NotInfinite
import Lemma.Rat.Gt0Div.of.Lt_0.Gt_0
import Lemma.Real.ExpSub.eq.DivExpS
open Hyperreal Real Rat


@[main]
private lemma main
  {a b : ℝ*}
-- given
  (h_sub : (a - b).Infinitesimal) :
-- imply
  a.exp ≈ b.exp := by
-- proof
  have h := Setoid.of.InfinitesimalSub h_sub
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
  else if h_b_neg : b.InfiniteNeg then
    have h_b := NotInfiniteNeg.of.NotInfiniteNeg.Setoid (Setoid.symm h) h_a
    contradiction
  else
    have h_a_exp := NotInfinitesimalExp.of.NotInfiniteNeg h_a
    have h_b_exp := NotInfinitesimalExp.of.NotInfiniteNeg h_b_neg
    simp [h_a_exp, h_b_exp]
    if h_a_pos : a.InfinitePos then
      have h_b_pos := InfinitePos.of.InfinitePos.Setoid h h_a_pos
      have h_div_exp := DivExpS.eq.ExpSub a b
      simp at h_div_exp
      have h_eps := OrAndS.of.Setoid h
      have h_a := NotInfinitesimal.of.InfinitePos h_a_pos
      have h_b := NotInfinitesimal.of.InfinitePos h_b_pos
      simp [h_a, h_b] at h_eps
      have h_st := EqSt.of.InfinitesimalSub h_eps
      rw [h_div_exp]
      apply InfinitesimalSub.of.EqSt.NotInfinite
      ·
        apply NotInfiniteExp.of.NotInfinitePos
        apply Hyperreal.NotInfinitePos.of.Infinitesimal h_sub
      ·
        rw [StExp.eq.ExpSt.of.NotInfinite]
        ·
          simp
          apply EqSt_0.of.Infinitesimal h_sub
        ·
          apply NotInfinite.of.Infinitesimal h_sub
    else if h_b_pos : b.InfinitePos then
      have h_a := Hyperreal.NotInfinite.of.NotInfinitePos.NotInfiniteNeg ⟨h_a_pos, h_a⟩
      have h_b := Infinite.of.InfinitePos h_b_pos
      have ⟨h_b, h_b_lt_0⟩ := Infinite.Gt_0.of.InfinitePos h_b_pos
      sorry
    else
      have h_b_inf := NotInfinite.of.NotInfinitePos.NotInfiniteNeg ⟨h_b_pos, h_b_neg⟩
      sorry


-- created on 2025-12-24
-- updated on 2025-12-28
