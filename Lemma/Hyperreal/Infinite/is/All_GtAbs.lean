import Mathlib.Analysis.Real.Hyperreal
import sympy.core.singleton
import Lemma.Int.Abs.eq.Neg.of.Lt_0
import Lemma.Int.Abs.ge.Neg
import Lemma.Int.EqAbs.of.Gt_0
import Lemma.Int.GeAbs
import Lemma.Int.GeAbs_0
import Lemma.Nat.Gt.of.Gt.Gt
import Lemma.Nat.Lt.of.Lt.Lt
open Int Nat


@[main, comm, mp, mpr]
private lemma main
-- given
  (x : ℝ*) :
-- imply
  x.Infinite ↔ ∀ δ : ℝ⁺, |x| > δ := by
-- proof
  unfold Hyperreal.Infinite
  constructor <;>
    intro h
  ·
    obtain h | h := h
    ·
      unfold Hyperreal.InfinitePos at h
      intro ⟨δ, hδ⟩
      simp
      have h := h δ
      convert h
      apply EqAbs.of.Gt_0
      apply Gt.of.Gt.Gt h
      simpa
    ·
      unfold Hyperreal.InfiniteNeg at h
      intro ⟨δ, hδ⟩
      simp
      have h := h (-δ)
      rw [Abs.eq.Neg.of.Lt_0]
      ·
        simp at h
        linarith
      ·
        apply Lt.of.Lt.Lt h
        simpa
  ·
    if h_x : x > 0 then
      left
      unfold Hyperreal.InfinitePos
      intro δ
      have h_δ := GeAbs_0 δ
      have h := h ⟨|δ| + 1, by linarith⟩
      simp at h
      have h_δ := GeAbs (δ : ℝ*)
      rw [EqAbs.of.Gt_0 h_x] at h
      linarith
    else if h_x : x < 0 then
      right
      unfold Hyperreal.InfiniteNeg
      intro δ
      have h_δ := GeAbs_0 δ
      have h := h ⟨|δ| + 1, by linarith⟩
      simp at h
      rw [Abs.eq.Neg.of.Lt_0 h_x] at h
      have h_δ := Abs.ge.Neg (δ : ℝ*)
      linarith
    else
      have h_x : x = 0 := by linarith
      subst h_x
      simp at h
      contrapose! h
      use 1
      simp


-- created on 2025-12-10
