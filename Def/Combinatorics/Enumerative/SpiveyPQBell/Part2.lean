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
import Theorem.Combinatorics.Enumerative.SpiveyPQBell.Part2
/-!
# The `(p, q)`-deformed Spivey formula

This file proves Oussi's addition formula for the `(p, q)`-Bell numbers.  The proof uses
the operator calculus of the source, interpreted on formal power series so that no analytic
convergence argument is needed.
-/


namespace MetaMathlibExt

open scoped BigOperators

noncomputable def spivey_Nop (p : ℝ) : Module.End ℝ (PowerSeries ℝ) where
  toFun := PowerSeries.rescale p
  map_add' f g := by
    exact map_add (PowerSeries.rescale p) f g
  map_smul' c f := by
    apply PowerSeries.ext
    intro i
    simp only [PowerSeries.coeff_rescale, PowerSeries.coeff_smul]
    change p ^ i * (c * PowerSeries.coeff i f) = c * (p ^ i * PowerSeries.coeff i f)
    ring

end MetaMathlibExt
