import Lemma.Hyperreal.Setoid.is.OrInfinitesimalSSub
open Hyperreal


@[main]
private lemma main
  {a b : ℝ*}
-- given
  (h : Infinitesimal (a - b)):
-- imply
  a ≈ b := by
-- proof
  simp_all [Setoid.is.OrInfinitesimalSSub]


-- created on 2025-12-27
