import Lemma.Hyperreal.InfiniteNeg.is.InfiniteNeg.of.Setoid
import Lemma.Hyperreal.InfinitePos.is.InfinitePos.of.Setoid
open Hyperreal


private lemma mp
  {a b : ℝ*}
-- given
  (h : a ≈ b)
  (h_a : a → ∞):
-- imply
  b → ∞ := by
-- proof
  obtain h_a | h_a := InfinitePos.ou.InfiniteNeg.of.Infinite h_a
  .
    apply Infinite.of.InfinitePos.ou.InfiniteNeg
    left
    exact InfinitePos.of.InfinitePos.Setoid h h_a.left h_a.right
  .
    apply Infinite.of.InfinitePos.ou.InfiniteNeg
    right
    exact InfiniteNeg.of.InfiniteNeg.Setoid h h_a.left h_a.right


@[main, mp, mp.mt]
private lemma main
  {a b : ℝ*}
-- given
  (h : a ≈ b) :
-- imply
  a → ∞ ↔ b → ∞ :=
-- proof
  ⟨mp h, mp h.symm⟩


-- created on 2025-12-27
