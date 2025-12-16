import Lemma.Hyperreal.InfinitesimalDiv.of.Infinitesimal.NotInfinitesimal
import Lemma.Hyperreal.EqSt_0.of.Infinitesimal
open Hyperreal


@[main]
private lemma main
  {a b : ℝ*}
-- given
  (h_st : st (a / b) ≠ 0)
  (h : a.Infinitesimal) :
-- imply
  b.Infinitesimal := by
-- proof
  apply Infinitesimal.of.Infinitesimal.NotInfinitesimalDiv h
  apply NotInfinitesimal.of.NeSt_0 h_st


-- created on 2025-12-16
