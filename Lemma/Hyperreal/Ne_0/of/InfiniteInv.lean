import Lemma.Hyperreal.Ne_0.of.Infinite
import Lemma.Rat.Eq_0.is.EqInv_0
open Hyperreal Rat


@[main]
private lemma main
  {x : ℝ*}
-- given
  (h : x⁻¹ → ∞) :
-- imply
  x ≠ 0 := by
-- proof
  apply Ne_0.of.NeInv_0
  apply Ne_0.of.Infinite h


-- created on 2025-12-17
