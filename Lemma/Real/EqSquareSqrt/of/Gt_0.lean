import sympy.core.power
import Lemma.Real.EqSquareSqrt.of.Ge_0
import Lemma.Nat.Ge.of.Gt
open Nat Real


@[main]
private lemma main
  {x : ℝ}
-- given
  (h : x > 0) :
-- imply
  (√x)² = x := by
-- proof
  have := Ge.of.Gt h
  apply EqSquareSqrt.of.Ge_0 this


-- created on 2025-04-06
