import Lemma.Hyperreal.EqSt
import Lemma.Hyperreal.EqSt.of.InfinitesimalSub
import Lemma.Hyperreal.EqSt_0.of.Infinite
import Lemma.Hyperreal.InfiniteDiv.of.Infinite.NotInfinite
import Lemma.Hyperreal.LeSt_0.of.Le_0
import Lemma.Hyperreal.NotInfiniteNeg.of.Infinitesimal
import Lemma.Hyperreal.Setoid.is.OrAndS
import Lemma.Rat.Gt0Div.of.Lt_0.Gt_0
open Hyperreal Rat


private lemma mp
  {a b : ℝ*}
-- given
  (h : a ≈ b)
  (h_a : a.InfiniteNeg):
-- imply
  b.InfiniteNeg := by
-- proof
  have h_or := OrAndS.of.Setoid h
  have h_a_eps := NotInfinitesimal.of.InfiniteNeg h_a
  simp [h_a_eps] at h_or
  let ⟨h_ab, h_b⟩ := h_or
  have h_st := EqSt.of.InfinitesimalSub h_ab
  have ⟨h_a, h_a_neg⟩ := Infinite.Lt_0.of.InfiniteNeg h_a
  if h_b_neg : b.InfiniteNeg then
    assumption
  else if h_b_pos : b.InfinitePos then
    have ⟨h_b, h_b_pos⟩ := Infinite.Gt_0.of.InfinitePos h_b_pos
    have h_ab := Gt0Div.of.Lt_0.Gt_0 h_a_neg h_b_pos
    have h_ab_st := LeSt_0.of.Le_0 (by linarith) (x := a / b)
    linarith
  else if h_b : b = 0 then
    subst h_b
    simp at h_st
    have := EqSt 0
    simp at this
    simp [this] at h_st
  else
    have : NeZero b := ⟨h_b⟩
    have h_b := NotInfinite.of.NotInfinitePos.NotInfiniteNeg ⟨h_b_pos, h_b_neg⟩
    have := InfiniteDiv.of.Infinite.NotInfinite h_a h_b
    have := EqSt_0.of.Infinite this
    linarith


@[main, mp, mp.mt]
private lemma main
  {a b : ℝ*}
-- given
  (h : a ≈ b) :
-- imply
  a.InfiniteNeg ↔ b.InfiniteNeg :=
-- proof
  ⟨mp h, mp (Setoid.symm h)⟩


-- created on 2025-12-27
