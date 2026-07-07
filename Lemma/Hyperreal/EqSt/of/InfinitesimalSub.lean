import Lemma.Hyperreal.IsSt.is.Le0Mk.EqStdPart
open Hyperreal


@[main]
private lemma main
  {x : ℝ*}
  {r : ℝ}
-- given
  (h : (x - r) → 0) :
-- imply
  stdPart x = r :=
-- proof
  (Le0Mk.EqStdPart.of.IsSt h).right


-- created on 2025-12-09
