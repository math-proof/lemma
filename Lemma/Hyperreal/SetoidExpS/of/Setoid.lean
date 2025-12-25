import Lemma.Hyperreal.InfiniteNeg.is.InfinitesimalExp
import Lemma.Hyperreal.NotInfinite.of.Infinitesimal
import Lemma.Hyperreal.Setoid.is.OrAndS
import sympy.functions.elementary.exponential
open Hyperreal


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
    if h_b : b.InfiniteNeg then
      have h_b_exp := InfinitesimalExp.of.InfiniteNeg h_b
      simp [h_b_exp]
    else
      have h_b_exp := NotInfinitesimalExp.of.NotInfiniteNeg h_b
      simp [h_b_exp]
      have ⟨h, h_b_eps⟩ := h
      have h_st := Hyperreal.EqSt.of.InfinitesimalSub h
      apply Hyperreal.InfinitesimalSub.of.EqSt.NotInfinite
      .
        sorry
      .
        sorry
  else
    sorry


-- created on 2025-12-24
-- updated on 2025-12-25
