import Lemma.Hyperreal.InfiniteNeg.is.InfiniteNeg.of.Setoid
import Lemma.Hyperreal.InfinitePos.is.InfinitePos.of.Setoid
open Hyperreal


private lemma mp
  {a b : ℝ*}
-- given
  (h : a ≈ b)
  (h_a : a.Infinite):
-- imply
  b.Infinite := by
-- proof
  obtain h_a | h_a := InfinitePos.ou.InfiniteNeg.of.Infinite h_a
  .
    apply Infinite.of.InfinitePos.ou.InfiniteNeg
    left
    exact InfinitePos.of.InfinitePos.Setoid h h_a
  .
    apply Infinite.of.InfinitePos.ou.InfiniteNeg
    right
    exact InfiniteNeg.of.InfiniteNeg.Setoid h h_a


@[main, mp, mp.mt]
private lemma main
  {a b : ℝ*}
-- given
  (h : a ≈ b) :
-- imply
  a.Infinite ↔ b.Infinite :=
-- proof
  ⟨mp h, mp (Setoid.symm h)⟩


-- created on 2025-12-27
