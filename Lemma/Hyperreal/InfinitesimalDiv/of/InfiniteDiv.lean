import Lemma.Hyperreal.Infinite.is.InfinitesimalInv
open Hyperreal


@[main]
private lemma main
  {a b : ℝ*}
-- given
  (h : (a / b) → ∞) :
-- imply
  (b / a) → 0 := by
-- proof
  have := InfinitesimalInv.of.Infinite h
  simp at this
  aesop


-- created on 2025-12-11
