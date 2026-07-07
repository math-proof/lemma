import Lemma.Hyperreal.InfiniteNeg.is.All_Lt
import Lemma.Hyperreal.InfiniteNeg.is.Infinite.Lt_0
import Lemma.Hyperreal.InfinitePos.is.All_Gt
import Lemma.Hyperreal.InfinitePos.is.Infinite.Gt_0
import Lemma.Int.Abs.eq.Neg.of.Lt_0
import Lemma.Int.EqAbs.of.Gt_0
open Hyperreal Int


@[main, comm, mp, mpr]
private lemma main
-- given
  (x : ℝ*) :
-- imply
  x → ∞ ↔ ∀ δ : ℝ⁺, |x| > δ := by
-- proof
  if h : x > 0 then
    constructor
    ·
      intro hInf ⟨δ, hδ⟩
      have hPos := (InfinitePos.is.Infinite.Gt_0 x).mpr ⟨hInf, h⟩
      have := (InfinitePos.is.All_Gt.pos x).mp hPos ⟨δ, hδ⟩
      simpa [EqAbs.of.Gt_0 h] using this
    ·
      intro hAbs
      refine ((InfinitePos.is.Infinite.Gt_0 x).mp ?_).1
      refine InfinitePos.of.All_Gt.pos ?_
      intro ⟨δ, hδ⟩
      simpa [EqAbs.of.Gt_0 h] using hAbs ⟨δ, hδ⟩
  else if h : x < 0 then
    constructor
    ·
      intro hInf ⟨δ, hδ⟩
      have hNeg := (InfiniteNeg.is.Infinite.Lt_0 x).mpr ⟨hInf, h⟩
      have hlt := (InfiniteNeg.is.All_Lt.neg x).mp hNeg ⟨-δ, by linarith⟩
      simp [Abs.eq.Neg.of.Lt_0 h] at hlt ⊢
      linarith [hlt, hδ]
    ·
      intro hAbs
      refine ((InfiniteNeg.is.Infinite.Lt_0 x).mp ?_).1
      refine InfiniteNeg.of.All_Lt.neg ?_
      intro ⟨δ, hδ⟩
      have hgt := hAbs ⟨-δ, by linarith⟩
      simp [Abs.eq.Neg.of.Lt_0 h] at hgt ⊢
      linarith [hgt, hδ]
  else
    have h : x = 0 := by linarith
    subst h
    simp_all
    use 1
    simp


-- created on 2025-12-10
-- updated on 2025-12-25
