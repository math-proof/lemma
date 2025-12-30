import Lemma.Int.Sub.lt.Zero.is.Lt
import Lemma.Hyperreal.InfinitePos.is.All_Gt
import Lemma.Hyperreal.Infinite.is.InfinitePos.ou.InfiniteNeg
import Lemma.Hyperreal.Infinite.is.InfiniteSub
import Lemma.Hyperreal.InfiniteNeg.is.Infinite.Lt_0
open Hyperreal Int


@[main, comm, mp, mpr]
private lemma main
-- given
  (x : ℝ*)
  (r : ℝ) :
-- imply
  x.InfinitePos ↔ (r - x).InfiniteNeg := by
-- proof
  rw [InfiniteNeg.is.Infinite.Lt_0]
  constructor <;>
    intro h
  .
    constructor
    .
      apply InfiniteSub.of.Infinite.left
      apply Infinite.of.InfinitePos h
    .
      apply Sub.lt.Zero.of.Lt
      apply All_Gt.of.InfinitePos h
  .
    let ⟨h_inf, h_neg⟩ := h
    have h_inf := Infinite.of.InfiniteSub.left h_inf
    have h_neg := Lt.of.Sub.lt.Zero h_neg
    obtain h_inf | h_inf := InfinitePos.ou.InfiniteNeg.of.Infinite h_inf
    .
      assumption
    .
      have h_all := All_Lt.of.InfiniteNeg h_inf r
      linarith


-- created on 2025-12-30
