import Lemma.Hyperreal.Infinitesimal0
open Hyperreal


@[main]
private lemma main
  {x : ℝ*}
-- given
  (h : ¬Infinitesimal x) :
-- imply
  x ≠ 0 := by
-- proof
  contrapose! h
  subst h
  apply Infinitesimal0


-- created on 2025-12-17
