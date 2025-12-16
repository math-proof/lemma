import Lemma.Hyperreal.EqSt.of.InfinitesimalSub
import Lemma.Hyperreal.IsSt.is.All_LtAbs
import Lemma.Int.LtAbs.is.LtNeg.Lt
open Hyperreal Int


@[main, mt]
private lemma main
  {x : ℝ*}
-- given
  (h : Infinitesimal x) :
-- imply
  st x = 0 :=
-- proof
  EqSt.of.InfinitesimalSub (x := x) (r := 0) (by simpa)


-- created on 2025-12-09
