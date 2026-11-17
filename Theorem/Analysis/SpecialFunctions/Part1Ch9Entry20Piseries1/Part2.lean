/-
Author: @akiezun, Avocado
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
public import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Def.Analysis.SpecialFunctions.Part1Ch9Entry20Piseries1.Part2

/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

public section


section

namespace Ramanujan.Part1Ch9

namespace Entry20Piseries1

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

theorem auxA_nonneg (k : ℕ) : 0 ≤ auxA k := by
  unfold auxA
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply mul_nonneg _ (sq_nonneg _)
  positivity

theorem auxA_le_one (k : ℕ) : auxA k ≤ 1 := by
  unfold auxA
  exact aux_coeff_le_one k

theorem auxA_zero : auxA 0 = 1 := by
  unfold auxA
  norm_num

theorem auxA_succ (k : ℕ) :
    auxA (k + 1) = auxA k * ((((2 * k + 2 : ℕ)) : ℝ) / ((((2 * k + 3 : ℕ)) : ℝ))) := by
  unfold auxA
  have hfact1 : (((k + 1).factorial : ℕ) : ℝ) = ((((k + 1 : ℕ)) : ℝ)) * ((k.factorial : ℝ)) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have heq : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
  have h3232 : (2 * k + 3 : ℕ) = (2 * k + 2) + 1 := by omega
  have h2221 : (2 * k + 2 : ℕ) = (2 * k + 1) + 1 := by omega
  have hfact2 : ((((2 * (k + 1) + 1).factorial : ℕ)) : ℝ) =
      ((((2 * k + 3 : ℕ)) : ℝ)) * ((((2 * k + 2 : ℕ)) : ℝ)) *
        ((((2 * k + 1).factorial : ℕ)) : ℝ) := by
    rw [heq, h3232, Nat.factorial_succ, h2221, Nat.factorial_succ]
    push_cast
    ring
  have hexp : 2 * (k + 1) = 2 * k + 2 := by ring
  have hpow : (2 : ℝ) ^ (2 * (k + 1)) = (2 : ℝ) ^ (2 * k) * 4 := by
    rw [hexp, pow_add]
    norm_num
  have hfk : ((((k + 1 : ℕ)) : ℝ)) = ((k : ℝ) + 1) := by push_cast; ring
  have h2k2 : ((((2 * k + 2 : ℕ)) : ℝ)) = 2 * ((k : ℝ) + 1) := by push_cast; ring
  have h2k3 : ((((2 * k + 3 : ℕ)) : ℝ)) = 2 * ((k : ℝ) + 1) + 1 := by push_cast; ring
  have hfact_ne : ((((2 * k + 1).factorial : ℕ)) : ℝ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h2k2_ne : ((((2 * k + 2 : ℕ)) : ℝ)) ≠ 0 := by
    apply Nat.cast_ne_zero.mpr
    omega
  have h2k3_ne : ((((2 * k + 3 : ℕ)) : ℝ)) ≠ 0 := by
    apply Nat.cast_ne_zero.mpr
    omega
  rw [hfact1, hfact2, hpow, hfk, h2k2, h2k3]
  field_simp
  ring

theorem auxA_rec (k : ℕ) :
    ((((2 * k + 3 : ℕ)) : ℝ)) * auxA (k + 1) = ((((2 * k + 2 : ℕ)) : ℝ)) * auxA k := by
  have h2k3_ne : ((((2 * k + 3 : ℕ)) : ℝ)) ≠ 0 := by
    apply Nat.cast_ne_zero.mpr
    omega
  rw [auxA_succ]
  field_simp

theorem aux_factorial_eq (u : ℝ) (k : ℕ) :
    chapter9Entry23FactorialTerm u k =
      auxA k * Real.sin u ^ (2 * k + 2) / ((((2 * k + 2 : ℕ)) : ℝ) ^ 2) := by
  unfold chapter9Entry23FactorialTerm auxA
  have hfact_ne : ((((2 * k + 1).factorial : ℕ)) : ℝ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h2k2_ne : ((((2 * k + 2 : ℕ)) : ℝ)) ≠ 0 := by
    apply Nat.cast_ne_zero.mpr
    omega
  field_simp

end
end Entry20Piseries1
end Ramanujan.Part1Ch9
end
