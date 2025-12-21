import Lemma.Hyperreal.EqSt
import Lemma.Hyperreal.EqSt_0.of.Infinitesimal
open Hyperreal


@[main, mt]
private lemma main
  {r : ℝ}
-- given
  (h : Infinitesimal r) :
-- imply
  r = 0 := by
-- proof
  contrapose! h
  apply NotInfinitesimal.of.NeSt_0
  rwa [EqSt]


-- created on 2025-12-21
