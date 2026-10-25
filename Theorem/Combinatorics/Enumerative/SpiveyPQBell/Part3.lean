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
import Def.Combinatorics.Enumerative.SpiveyPQBell.Part2
/-!
# The `(p, q)`-deformed Spivey formula

This file proves Oussi's addition formula for the `(p, q)`-Bell numbers.  The proof uses
the operator calculus of the source, interpreted on formal power series so that no analytic
convergence argument is needed.
-/


namespace MetaMathlibExt

open scoped BigOperators

lemma spivey_Nop_apply (p : ℝ) (f : PowerSeries ℝ) :
    spivey_Nop p f = PowerSeries.rescale p f := rfl

lemma spivey_Nop_pow_apply (p : ℝ) (a : ℕ) (f : PowerSeries ℝ) :
    ((spivey_Nop p) ^ a) f = PowerSeries.rescale (p ^ a) f := by
  induction a generalizing f with
  | zero =>
      simp
  | succ a ih =>
      rw [pow_succ, Module.End.mul_apply, spivey_Nop_apply, ih,
        PowerSeries.rescale_rescale]
      congr 1
      rw [pow_succ]
      ring_nf

end MetaMathlibExt
