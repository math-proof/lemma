import Lemma.Hyperreal.InfiniteInfty
import Lemma.Hyperreal.InfinitesimalDiv.of.Infinite
import Lemma.Hyperreal.NeInfty0
import Lemma.Hyperreal.NotInfinitesimalInfty
import Lemma.Hyperreal.Setoid.is.OrAndS
import Lemma.Rat.DivAdd.eq.AddDiv.of.Ne_0
open Hyperreal Rat


@[main]
private lemma main
-- given
  (x : ℝ) :
-- imply
  x + Hyperreal.omega ≈ Hyperreal.omega := by
-- proof
  apply Setoid.of.OrAndS
  right
  constructor
  ·
    rw [DivAdd.eq.AddDiv.of.Ne_0 NeInfty0]
    simp
    apply InfinitesimalDiv.of.Infinite
    apply InfiniteInfty
  ·
    exact NotInfinitesimalInfty


-- created on 2025-12-08
-- updated on 2025-12-16
