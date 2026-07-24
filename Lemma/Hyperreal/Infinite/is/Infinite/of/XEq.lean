import Lemma.Hyperreal.InfiniteNeg.is.InfiniteNeg.of.XEq
import Lemma.Hyperreal.InfinitePos.is.InfinitePos.of.XEq
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
    exact InfinitePos.of.InfinitePos.XEq h h_a
  .
    apply Infinite.of.InfinitePos.ou.InfiniteNeg
    right
    exact InfiniteNeg.of.InfiniteNeg.XEq h h_a


/--
| attributes | lemma |
| :---: | :---: |
| main | Hyperreal.Infinite.is.Infinite.of.XEq |
| mp   | Hyperreal.Infinite.of.Infinite.XEq |
| mp.mt | Hyperreal.NotInfinite.of.NotInfinite.XEq |
-/
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
