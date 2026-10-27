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
import Def.Analysis.SpecialFunctions.Part1Ch5Entry2iEuleriangf.Part6
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

theorem hwe : psE + psEb - 2 =
    (-2 : ℝ) • psW := by
  have hCCmul : (-2 : ℝ) * (1 / 2) = -1 := by norm_num
  have hCC : (PowerSeries.C (-2 : ℝ)) * (PowerSeries.C (1 / 2 : ℝ)) = -1 := by
    rw [← map_mul, hCCmul]
    simp
  have hC2 : (PowerSeries.C (2 : ℝ)) = 2 := rfl
  have hCm2 : (PowerSeries.C (-2 : ℝ)) = -2 := by
    rw [show (-2 : ℝ) = -(2 : ℝ) from rfl, map_neg, hC2]
  have hneg1 : (-1 : PowerSeries ℝ) *
        (psE + psEb) =
      -(psE + psEb) := by
    rw [neg_mul, one_mul]
  rw [Algebra.smul_def, PowerSeries.algebraMap_eq]
  unfold psW
  rw [mul_sub, mul_one, ← mul_assoc, hCC, hCm2, hneg1, sub_neg_eq_add]
  abel

theorem hbeta (n : ℕ) :
    (((-1 : ℝ) ^ n * ((n.factorial : ℝ) ^ 2) / ((2 * n).factorial : ℝ)) * (-2 : ℝ) ^ n) =
      psBeta n := by
  have h2n : (-1 : ℝ) ^ n * (-2 : ℝ) ^ n = 2 ^ n := by
    rw [← mul_pow]
    norm_num
  have hF : ((2 * n).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  unfold psBeta
  rw [show (-1 : ℝ) ^ n * (n.factorial : ℝ) ^ 2 / ((2 * n).factorial : ℝ) * (-2 : ℝ) ^ n =
    ((-1 : ℝ) ^ n * (-2 : ℝ) ^ n) * ((n.factorial : ℝ) ^ 2 / ((2 * n).factorial : ℝ)) from by ring,
    h2n]
  ring

theorem entry2F_eq_smul_psAct (phi : ℝ[X]) (n M : ℕ) (hM : phi.natDegree < M) :
    chapter5Entry2F phi n = psBeta n • psAct M (psW ^ n) phi := by
  have hN7 := n7_full (psE) (psEb)
    exp_mul_rescale_neg_eq_one n
  have hbridge : (psE + psEb - 2) ^ n =
      ((-2 : ℝ) ^ n) • psW ^ n := by
    rw [hwe, smul_pow]
  have hbeta' : (((-1 : ℝ) ^ n * ((n.factorial : ℝ) ^ 2) / ((2 * n).factorial : ℝ)) *
      (-2 : ℝ) ^ n) • psAct M (psW ^ n) phi = psBeta n • psAct M (psW ^ n) phi := by
    rw [hbeta n]
  have key : psAct M (1 + ∑ k ∈ Finset.Icc 1 n,
      (((-1 : ℝ) ^ k * ((n.factorial : ℝ) ^ 2) /
        (((n + k).factorial : ℝ) * ((n - k).factorial : ℝ))) •
        (psE ^ k + psEb ^ k))) phi =
      chapter5Entry2F phi n := by
    rw [psAct_add, LinearMap.add_apply, psAct_sum, LinearMap.sum_apply, psAct_one M phi hM]
    unfold chapter5Entry2F
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [psAct_smul, LinearMap.smul_apply, psAct_add, LinearMap.add_apply,
      psAct_exp_pow_shift M k phi hM, psAct_ebar_pow_shift M k phi hM,
      smul_add, Polynomial.smul_eq_C_mul, Polynomial.smul_eq_C_mul, ← mul_add]
  rw [← key, hN7, hbridge, psAct_smul, LinearMap.smul_apply, psAct_smul,
    LinearMap.smul_apply, ← mul_smul]
  exact hbeta'

theorem psW_pow_dvd (n : ℕ) : PowerSeries.X ^ (2 * n) ∣ psW ^ n := by
  have hC2 : (2 : PowerSeries ℝ) = PowerSeries.C 2 := rfl
  have hC12 : PowerSeries.C (1 / 2 : ℝ) * 2 = 1 := by
    rw [hC2, ← map_mul]
    norm_num
  have h2 : PowerSeries.X ^ 2 ∣ psW := by
    have hneg : PowerSeries.C (-1 / 2 : ℝ) = -PowerSeries.C (1 / 2 : ℝ) := by
      rw [show (-1 / 2 : ℝ) = -(1 / 2) from by ring, map_neg]
    have hsub : psW = PowerSeries.C (-1 / 2 : ℝ) *
        (psE + psEb - 2) := by
      unfold psW
      rw [hneg, neg_mul, mul_sub, neg_sub, hC12]
    rw [hsub]
    exact Dvd.dvd.mul_left exp_add_rescale_sub_two _
  have h3 : (PowerSeries.X ^ 2) ^ n ∣ psW ^ n := pow_dvd_pow_of_dvd h2 n
  rwa [pow_mul]

theorem entry2F_eq_zero_of_natDegree_lt (phi : ℝ[X]) (n : ℕ)
    (hlt : phi.natDegree < 2 * n) : chapter5Entry2F phi n = 0 := by
  have hM : phi.natDegree < phi.natDegree + 1 := Nat.lt_succ_self _
  rw [entry2F_eq_smul_psAct phi n (phi.natDegree + 1) hM]
  have hkill : psAct (phi.natDegree + 1) (psW ^ n) phi = 0 := by
    apply psAct_eq_zero_of_X_pow_dvd _ _ _ (psW_pow_dvd n) hlt
  rw [hkill, _root_.smul_zero]

end
end Entry2iEuleriangf
end Ramanujan.Part1Ch5
end
