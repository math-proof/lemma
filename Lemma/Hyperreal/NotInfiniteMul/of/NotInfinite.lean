import Lemma.Hyperreal.NotInfinite
import Lemma.Hyperreal.NotInfiniteMul.of.NotInfinite.NotInfinite
import Lemma.Nat.Mul
open Hyperreal Nat


@[main]
private lemma main
  {x : ℝ*}
-- given
  (h : ¬x.Infinite)
  (r : ℝ) :
-- imply
  ¬Infinite (x * r) := by
-- proof
  apply NotInfiniteMul.of.NotInfinite.NotInfinite h
  apply NotInfinite


@[main]
private lemma left
  {x : ℝ*}
-- given
  (r : ℝ)
  (h : ¬x.Infinite) :
-- imply
  ¬Infinite (r * x) := by
-- proof
  rw [Mul.comm]
  apply main h


-- created on 2025-12-17
