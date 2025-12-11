import Lemma.Hyperreal.NotInfinitesimalSub.of.Infinitesimal.Ne_0
open Hyperreal


@[main]
private lemma main
  {x : ℝ*}
  {r : ℝ}
-- given
  (h : Infinitesimal x)
  (h_r : r ≠ 0) :
-- imply
  ¬Infinitesimal (x + r) := by
-- proof
  have := NotInfinitesimalSub.of.Infinitesimal.Ne_0 h (by simpa) (r := -r)
  simp at this
  assumption


-- created on 2025-12-11
