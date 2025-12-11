import Lemma.Hyperreal.InfiniteAdd.of.Infinite
open Hyperreal


@[main]
private lemma main
  {x : ℝ*}
-- given
  (h : Infinite x)
  (r : ℝ) :
-- imply
  Infinite (x - r) := by
-- proof
  have := InfiniteAdd.of.Infinite h (-r)
  simp at this
  assumption


-- created on 2025-12-11
