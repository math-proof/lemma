import Lemma.Hyperreal.XEq.is.OrInfinitesimalSSub
open Hyperreal


@[main]
private lemma main
  {a b : ℝ*}
-- given
  (h : (a - b) → 0) :
-- imply
  a ≈ b := by
-- proof
  simp_all [XEq.is.OrInfinitesimalSSub]


-- created on 2025-12-27
