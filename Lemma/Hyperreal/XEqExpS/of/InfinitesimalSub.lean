import Lemma.Hyperreal.Infinite.is.InfiniteSub.of.NotInfinite
import Lemma.Hyperreal.Infinite.is.InfinitePos.ou.InfiniteNeg
import Lemma.Hyperreal.EqSt.of.InfinitesimalSub
import Lemma.Hyperreal.EqSt_0.of.Infinite
import Lemma.Hyperreal.EqSt_0.of.Infinitesimal
import Lemma.Hyperreal.InfiniteDiv.of.Infinite.NotInfinite
import Lemma.Hyperreal.InfiniteNeg.is.InfiniteNeg.of.XEq
import Lemma.Hyperreal.InfiniteNeg.is.InfinitesimalExp
import Lemma.Hyperreal.InfinitePos.is.InfiniteExp
import Lemma.Hyperreal.InfinitePos.is.InfinitePos.of.XEq
import Lemma.Hyperreal.InfinitesimalSub.of.EqSt.NotInfinite
import Lemma.Hyperreal.LeSt_0.of.Le_0
import Lemma.Hyperreal.Ne_0.of.NotInfinitesimal
import Lemma.Hyperreal.NotInfinite.of.Infinitesimal
import Lemma.Hyperreal.NotInfinitePos.of.Infinitesimal
import Lemma.Hyperreal.XEq.is.OrAndS
import Lemma.Hyperreal.XEq.of.InfinitesimalSub
import Lemma.Hyperreal.StExp.eq.ExpSt.of.NotInfinite
import Lemma.Rat.Gt0Div.of.Lt_0.Gt_0
import Lemma.Real.ExpSub.eq.DivExpS
open Hyperreal Real Rat


@[main]
private lemma main
  {a b : ℝ*}
-- given
  (h_sub : (a - b) → 0) :
-- imply
  a.exp ≈ b.exp := by
-- proof
  have h := XEq.of.InfinitesimalSub h_sub
  apply XEq.of.OrAndS
  if h_a_neg : a → -∞ then
    have h_a_exp := InfinitesimalExp.of.InfiniteNeg h_a_neg
    simp [h_a_exp]
    have h := OrAndS.of.XEq h
    have ⟨h_a, h_a_neg⟩ := Infinite.Lt_0.of.InfiniteNeg h_a_neg
    simp [NotInfinitesimal.of.Infinite h_a] at h
    have ⟨h, h_b_eps⟩ := h
    have h_st := EqSt.of.InfinitesimalSub h
    if h_b_neg : b → -∞ then
      have h_b_exp := InfinitesimalExp.of.InfiniteNeg h_b_neg
      simp [h_b_exp]
    else if h_b_pos : b → +∞ then
      have ⟨h_b, h_b_neg⟩ := Infinite.Gt_0.of.InfinitePos h_b_pos
      have h_ab := Gt0Div.of.Lt_0.Gt_0 h_a_neg h_b_neg
      have := LeSt_0.of.Le_0 (by linarith) (x := a / b)
      linarith
    else
      have h_b_inf := NotInfinite.of.NotInfinitePos.NotInfiniteNeg ⟨h_b_pos, h_b_neg⟩
      have : NeZero b := ⟨Ne_0.of.NotInfinitesimal (not_lt.mpr h_b_eps)⟩
      have := InfiniteDiv.of.Infinite.NotInfinite h_a h_b_inf
      have := EqSt_0.of.Infinite this
      linarith
  else if h_b_neg : b → -∞ then
    have h_b := NotInfiniteNeg.of.NotInfiniteNeg.XEq h.symm h_b_neg.left h_a_neg
    exact False.elim (h_b h_b_neg.right)
  else
    have h_a_exp := NotInfinitesimalExp.of.NotInfiniteNeg h_a_neg
    have h_b_exp := NotInfinitesimalExp.of.NotInfiniteNeg h_b_neg
    simp [h_a_exp, h_b_exp]
    have h_div_exp := DivExpS.eq.ExpSub a b
    simp at h_div_exp
    rw [h_div_exp]
    if h_a_pos : a → +∞ then
      have h_b_pos := InfinitePos.of.InfinitePos.XEq h h_a_pos
      have h_eps := OrAndS.of.XEq h
      have h_a := NotInfinitesimal.of.InfinitePos h_a_pos
      have h_b := NotInfinitesimal.of.InfinitePos h_b_pos
      simp [h_a, h_b] at h_eps
      have h_st := EqSt.of.InfinitesimalSub h_eps
      apply InfinitesimalSub.of.EqSt.NotInfinite
      ·
        apply NotInfiniteExp.of.NotInfinitePos
        exact NotInfinitePos.of.Infinitesimal h_sub
      ·
        rw [StExp.eq.ExpSt.of.NotInfinite]
        ·
          simp [Real.exp_zero, EqSt_0.of.Infinitesimal h_sub]
        ·
          exact NotInfinite.of.Infinitesimal h_sub
    else if h_b_pos : b → +∞ then
      have h_a := NotInfinite.of.NotInfinitePos.NotInfiniteNeg ⟨h_a_pos, h_a_neg⟩
      have h_b := Infinite.of.InfinitePos h_b_pos
      have h_sub := InfiniteSub.of.Infinite.NotInfinite h_a h_b
      have h_sub := NotInfinitesimal.of.Infinite h_sub
      contradiction
    else
      apply InfinitesimalSub.of.EqSt.NotInfinite
      .
        apply NotInfiniteExp.of.NotInfinitePos
        apply NotInfinitePos.of.Infinitesimal h_sub
      .
        rw [StExp.eq.ExpSt.of.NotInfinite]
        .
          simp [EqSt_0.of.Infinitesimal h_sub]
        .
          apply NotInfiniteSub.of.NotInfinite.NotInfinite
          .
            exact NotInfinite.of.NotInfinitePos.NotInfiniteNeg ⟨h_a_pos, h_a_neg⟩
          .
            exact NotInfinite.of.NotInfinitePos.NotInfiniteNeg ⟨h_b_pos, h_b_neg⟩


-- created on 2025-12-24
-- updated on 2025-12-28
