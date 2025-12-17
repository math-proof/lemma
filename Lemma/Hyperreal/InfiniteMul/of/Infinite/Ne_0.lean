import Lemma.Hyperreal.InfiniteDiv.of.Infinite.Ne_0
import Lemma.Rat.Ne_0.is.NeInv_0
open Hyperreal Rat


@[main]
private lemma main
  {x : ℝ*}
  {r : ℝ}
-- given
  (h : Infinite x)
  (h_r : r ≠ 0) :
-- imply
  Infinite (x * r) := by
-- proof
  have h_r := NeInv_0.of.Ne_0 h_r
  have := InfiniteDiv.of.Infinite.Ne_0 h h_r
  simp_all


-- created on 2025-12-11
