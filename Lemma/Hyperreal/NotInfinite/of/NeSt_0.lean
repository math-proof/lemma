import Mathlib.Analysis.Real.Hyperreal
import sympy.Basic
open Hyperreal (st Infinite)


@[main]
private lemma main
  {x : ℝ*}
-- given
  (h : st x ≠ 0) :
-- imply
  ¬Infinite x :=
-- proof
  mt Hyperreal.Infinite.st_eq h


-- created on 2025-12-09
