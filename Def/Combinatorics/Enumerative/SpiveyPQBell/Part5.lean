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
public import Theorem.Combinatorics.Enumerative.SpiveyPQBell.Part5


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/SpiveyPQBell.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
/-!
# The `(p, q)`-deformed Spivey formula

This file proves Oussi's addition formula for the `(p, q)`-Bell numbers.  The proof uses
the operator calculus of the source, interpreted on formal power series so that no analytic
convergence argument is needed.
-/
namespace MetaMathlibExt

open scoped BigOperators

noncomputable def spivey_ecoeff (p : ℝ) (bracket : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | i + 1 => p ^ i / bracket (i + 1) * spivey_ecoeff p bracket i

noncomputable def spivey_E (p : ℝ) (bracket : ℕ → ℝ) : PowerSeries ℝ :=
  PowerSeries.mk (spivey_ecoeff p bracket)

end MetaMathlibExt
