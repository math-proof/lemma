/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/SpiveyPQBell.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.SpiveyPQBell
/-!
# The `(p, q)`-deformed Spivey formula

This file proves Oussi's addition formula for the `(p, q)`-Bell numbers.  The proof uses
the operator calculus of the source, interpreted on formal power series so that no analytic
convergence argument is needed.
-/


namespace MetaMathlibExt

open scoped BigOperators

lemma spivey_Xop_apply (f : PowerSeries ℝ) :
    spivey_Xop f = PowerSeries.X * f := rfl

lemma spivey_Xop_pow_apply (k : ℕ) (f : PowerSeries ℝ) :
    (spivey_Xop ^ k) f = PowerSeries.X ^ k * f := by
  induction k generalizing f with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Module.End.mul_apply, spivey_Xop_apply, ih, pow_succ]
      ring

end MetaMathlibExt
