import Lemma.Hyperreal.EqSt.of.InfinitesimalSub
import Lemma.Hyperreal.IsSt.is.All_LtAbs
import Lemma.Int.LtAbs.is.LtNeg.Lt
open Hyperreal Int


/--
| attributes | lemma |
| :---: | :---: |
| main | Hyperreal.EqSt_0.of.Infinitesimal |
| mt | Hyperreal.NotInfinitesimal.of.NeSt_0 |
-/
@[main, mt]
private lemma main
  {x : ℝ*}
-- given
  (h : x → 0) :
-- imply
  stdPart x = 0 :=
-- proof
  EqSt.of.InfinitesimalSub (x := x) (r := 0) (by simpa)


-- created on 2025-12-09
