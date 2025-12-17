import Lemma.Hyperreal.Ne_0.of.Infinite
import Lemma.Rat.Ne_0.is.NeInv_0
open Hyperreal Rat


@[main]
private lemma main
  {x : ℝ*}
-- given
  (h : x⁻¹.Infinite) :
-- imply
  x ≠ 0 := by
-- proof
  have h := Ne_0.of.Infinite h
  apply Ne_0.of.NeInv_0 h


-- created on 2025-12-17
