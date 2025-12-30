import Lemma.Hyperreal.InfiniteNeg.is.All_Lt
import Lemma.Hyperreal.InfiniteNeg.is.Infinite.Lt_0
import Lemma.Hyperreal.InfinitePos.is.All_Gt
import Lemma.Hyperreal.InfinitePos.is.Infinite.Gt_0
import Lemma.Hyperreal.NotInfinite
import Lemma.Int.Abs.eq.Neg.of.Lt_0
import Lemma.Int.EqAbs.of.Gt_0
import sympy.core.singleton
open Hyperreal Int


@[main, comm, mp, mpr]
private lemma main
-- given
  (x : ℝ*) :
-- imply
  x.Infinite ↔ ∀ δ : ℝ⁺, |x| > δ := by
-- proof
  if h : x > 0 then
    have h' := InfinitePos.is.Infinite.Gt_0 x
    simp [h] at h'
    rw [← h']
    rw [InfinitePos.is.All_Gt.pos]
    rw [EqAbs.of.Gt_0 h]
  else if h : x < 0 then
    have h' := InfiniteNeg.is.Infinite.Lt_0 x
    simp [h] at h'
    rw [← h']
    rw [InfiniteNeg.is.All_Lt.neg]
    rw [Abs.eq.Neg.of.Lt_0 h]
    constructor <;>
    ·
      intro h ⟨δ, hδ⟩
      simp
      have h := h ⟨-δ, by linarith⟩
      simp at h
      linarith
  else
    have h : x = 0 := by linarith
    subst h
    simp_all
    have := NotInfinite 0
    simp at this
    simp [this]
    use 1
    simp


-- created on 2025-12-10
-- updated on 2025-12-25
