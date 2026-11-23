/-
Author: @akiezun, Avocado
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.NatFactorial
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Def.Analysis.SpecialFunctions.Part1Ch5Entry2iEuleriangf.Part4

@[expose] public section

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
