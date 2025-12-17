import Lemma.Hyperreal.NotInfinite
open Hyperreal


@[main]
private lemma main
  {x : ℝ*}
-- given
  (h : x.Infinite) :
-- imply
  x ≠ 0 := by
-- proof
  contrapose! h
  subst h
  apply NotInfinite


-- created on 2025-12-17
