import Lemma.Hyperreal.Infinitesimal0
open Hyperreal


@[path]
private lemma main
  {x : ℝ*}
-- given
  (h : x → 0⁺) :
-- imply
  x ≠ 0 := by
-- proof
  contrapose! h
  subst h
  grind


-- created on 2025-12-11
-- updated on 2026-11-05
