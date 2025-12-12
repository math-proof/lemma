import Lemma.Hyperreal.EqSt_0.of.Infinite
open Hyperreal


@[main]
private lemma main
  {x : ℝ*}
-- given
  (h : st x ≠ 0) :
-- imply
  ¬Infinite x :=
-- proof
  mt EqSt_0.of.Infinite h


-- created on 2025-12-09
-- updated on 2025-12-12
