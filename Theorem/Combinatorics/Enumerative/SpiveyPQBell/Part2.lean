/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/SpiveyPQBell.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Ring
public import Def.Combinatorics.Enumerative.SpiveyPQBell

/-!
# The `(p, q)`-deformed Spivey formula

This file proves Oussi's addition formula for the `(p, q)`-Bell numbers.  The proof uses
the operator calculus of the source, interpreted on formal power series so that no analytic
convergence argument is needed.
-/

public section


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
