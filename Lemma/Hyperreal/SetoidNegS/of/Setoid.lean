import Lemma.Hyperreal.Infinitesimal.is.InfinitesimalNeg
import Lemma.Hyperreal.Setoid.is.OrAndS
import Lemma.Rat.DivNegS.eq.Div
open Hyperreal Rat


@[main]
private lemma main
  {x y : ℝ*}
-- given
  (h : x ≈ y) :
-- imply
  -x ≈ -y := by
-- proof
  apply Setoid.of.OrAndS
  repeat rw [InfinitesimalNeg.is.Infinitesimal]
  rw [DivNegS.eq.Div]
  exact OrAndS.of.Setoid h


-- created on 2025-12-23
