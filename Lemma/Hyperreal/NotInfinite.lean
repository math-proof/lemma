import sympy.series.limits
import Lemma.Nat.NotLt.of.Ge
open Nat


@[main]
private lemma main
-- given
  (x : ℝ) :
-- imply
  ¬(x : ℝ*) → ∞ :=
-- proof
  NotLt.of.Ge (Hyperreal.archimedeanClassMk_coe_nonneg x)


-- created on 2025-12-11
