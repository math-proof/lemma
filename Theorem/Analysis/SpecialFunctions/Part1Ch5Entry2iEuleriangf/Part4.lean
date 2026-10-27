/-
Author: @akiezun, Avocado
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Squarefree
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Def.Analysis.SpecialFunctions.Part1Ch5Entry2iEuleriangf.Part4
/-!
# Ramanujan's Notebooks, Part I, Chapter 5

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace Ramanujan.Part1Ch5

namespace Entry2iEuleriangf

open scoped Nat Real BigOperators Interval Polynomial

open Finset

noncomputable section

theorem psC_recurrence (N : ℕ) : (2 * N + 3 : ℝ) * psC (N + 1) = ((N + 1 : ℕ) : ℝ) * psC
    N := by
  unfold psC
  have e1 : 2 * (N + 1) + 1 = (2 * N + 2) + 1 := by ring
  have e2 : 2 * N + 2 = (2 * N + 1) + 1 := by ring
  rw [e1, Nat.factorial_succ (2 * N + 2), e2, Nat.factorial_succ (2 * N + 1),
    Nat.factorial_succ N, pow_succ (2 : ℝ) N]
  have hF1 : ((2 * N + 1).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hF2 : ((N.factorial : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  push_cast
  field_simp
  ring

theorem ode_step (a : ℝ) (m : ℕ) :
    (1 - Polynomial.X) * (Polynomial.C a * Polynomial.X ^ (m + 1)) +
      (2 * Polynomial.X - Polynomial.X ^ 2) *
        Polynomial.derivative (Polynomial.C a * Polynomial.X ^ (m + 1)) =
      Polynomial.C ((2 * m + 3) * a) * Polynomial.X ^ (m + 1) -
        Polynomial.C ((m + 2) * a) * Polynomial.X ^ (m + 2) := by
  have c1 : Polynomial.C a + 2 * Polynomial.C (a * ((m + 1 : ℕ) : ℝ)) =
      Polynomial.C ((2 * m + 3) * a) := by
    rw [two_mul, ← Polynomial.C_add, ← Polynomial.C_add]
    congr 1
    push_cast
    ring
  have c2 : Polynomial.C a + Polynomial.C (a * ((m + 1 : ℕ) : ℝ)) =
      Polynomial.C ((m + 2) * a) := by
    rw [← Polynomial.C_add]
    congr 1
    push_cast
    ring
  rw [Polynomial.derivative_C_mul, Polynomial.derivative_X_pow, Nat.add_sub_cancel,
    ← mul_assoc (Polynomial.C a) _ _, ← Polynomial.C_mul]
  linear_combination (Polynomial.X ^ (m + 1)) * c1 - (Polynomial.X ^ (m + 2)) * c2

end
end Entry2iEuleriangf
end Ramanujan.Part1Ch5
end
