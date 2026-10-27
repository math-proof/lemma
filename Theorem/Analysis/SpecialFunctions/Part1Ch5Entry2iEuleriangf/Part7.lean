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
import Def.Analysis.SpecialFunctions.Part1Ch5Entry2iEuleriangf.Part7
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

theorem psC2 : (2 : PowerSeries ℝ) = PowerSeries.C 2 := rfl

theorem psC4 : (4 : PowerSeries ℝ) = PowerSeries.C 4 := rfl

theorem h2C12 : (2 : PowerSeries ℝ) * PowerSeries.C (1 / 2 : ℝ) = 1 := by
  rw [psC2, ← map_mul]
  norm_num [map_one]

theorem hC14 : PowerSeries.C (1 / 2 : ℝ) * 4 = PowerSeries.C (2 : ℝ) := by
  rw [psC4, ← map_mul]
  norm_num

theorem h2cC : PowerSeries.C (1 / 2 : ℝ) * PowerSeries.C (2 : ℝ) = 1 := by
  rw [← map_mul]
  norm_num [map_one]

theorem psB2 : psE + psEb =
    2 * (1 - psW) := by
  have e1 : 1 - psW = PowerSeries.C (1 / 2 : ℝ) *
      (psE + psEb) := by
    unfold psW
    ring
  rw [e1, ← mul_assoc, h2C12, one_mul]

theorem psB2C : psE + psEb =
    PowerSeries.C (2 : ℝ) * (1 - psW) := by
  have h := psB2
  rwa [psC2] at h

theorem pssq : (psE - psEb) *
    (psE - psEb) =
    (psE + psEb) *
      (psE + psEb) - 4 :=
  by linear_combination (-4) * exp_mul_rescale_neg_eq_one

theorem psDs : PowerSeries.derivative
    (psE - psEb) =
    psE + psEb := by
  rw [map_sub, PowerSeries.derivative_exp, derivative_rescale_neg_exp, sub_neg_eq_add]

theorem psDw : PowerSeries.derivative psW =
    -(PowerSeries.C (1 / 2 : ℝ) *
      (psE - psEb)) := by
  have e1 : PowerSeries.derivative
      (PowerSeries.C (1 / 2 : ℝ) *
        (psE + psEb)) =
      PowerSeries.C (1 / 2 : ℝ) *
        (psE + -psEb) := by
    rw [Derivation.leibniz, PowerSeries.derivative_C, map_add, PowerSeries.derivative_exp,
      derivative_rescale_neg_exp, smul_eq_mul, smul_eq_mul, mul_zero, add_zero]
  have e0 : (1 : PowerSeries ℝ) = PowerSeries.C (1 : ℝ) := (map_one PowerSeries.C).symm
  unfold psW
  rw [map_sub, e0, PowerSeries.derivative_C, e1, zero_sub, sub_eq_add_neg]

theorem psD2X : PowerSeries.derivative (PowerSeries.C (2 : ℝ) * PowerSeries.X) =
    PowerSeries.C (2 : ℝ) := by
  rw [Derivation.leibniz, PowerSeries.derivative_X, PowerSeries.derivative_C, smul_eq_mul,
    smul_eq_mul, mul_one, mul_zero, add_zero]

theorem psMapped (N : ℕ) : (1 - psW) * psY N +
    (PowerSeries.C (2 : ℝ) * psW - psW * psW) *
      Polynomial.aeval psW (Polynomial.derivative (psYpoly N)) =
    1 - PowerSeries.C (((N + 1 : ℕ) : ℝ) * psC N) * psW ^ (N + 1) := by
  have hN10 := arcsin_poly_ode N
  have hmap := congrArg (Polynomial.aeval psW) hN10
  simp only [map_add, map_sub, map_mul, map_one, Polynomial.aeval_X, map_pow,
    Polynomial.aeval_C, PowerSeries.algebraMap_eq] at hmap
  rw [map_ofNat, pow_two, ← map_mul, psC2] at hmap
  unfold psY
  linear_combination hmap

theorem cC2bridge : PowerSeries.C (1 / 2 : ℝ) *
    (PowerSeries.C (2 : ℝ) * PowerSeries.C (2 : ℝ)) = PowerSeries.C (2 : ℝ) := by
  rw [← mul_assoc, h2cC, one_mul]

theorem psBCOMB : PowerSeries.C (1 / 2 : ℝ) *
    ((psE + psEb) *
      (psE + psEb)) =
    PowerSeries.C (2 : ℝ) * ((1 - psW) * (1 - psW)) := by
  rw [psB2C, show PowerSeries.C (1 / 2 : ℝ) *
      ((PowerSeries.C (2 : ℝ) * (1 - psW)) * (PowerSeries.C (2 : ℝ) * (1 - psW))) =
      (PowerSeries.C (1 / 2 : ℝ) * (PowerSeries.C (2 : ℝ) * PowerSeries.C (2 : ℝ))) *
        ((1 - psW) * (1 - psW)) from by ring, cC2bridge]

theorem psDeriv (N : ℕ) : PowerSeries.derivative (psG N) =
    -(PowerSeries.C (2 : ℝ) * PowerSeries.C (((N + 1 : ℕ) : ℝ) * psC N)) * psW ^ (N + 1) := by
  have E1 : PowerSeries.derivative (psG N) =
      PowerSeries.derivative ((psE -
        psEb) * psY N) -
        PowerSeries.derivative (PowerSeries.C (2 : ℝ) * PowerSeries.X) := by
    unfold psG
    rw [map_sub]
  have E2 : PowerSeries.derivative
      ((psE - psEb) * psY N) =
      (psE - psEb) *
        PowerSeries.derivative (psY N) +
        psY N * PowerSeries.derivative
          (psE - psEb) := by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  have E4 : PowerSeries.derivative (psY N) =
      Polynomial.aeval psW (Polynomial.derivative (psYpoly N)) *
        PowerSeries.derivative psW := by
    unfold psY
    rw [Derivation.map_aeval, smul_eq_mul]
  linear_combination E1 + E2 +
    (psE - psEb) * E4 +
    psY N * psDs +
    ((psE - psEb) *
      Polynomial.aeval psW (Polynomial.derivative (psYpoly N))) * psDw -
    psD2X +
    (-(PowerSeries.C (1 / 2 : ℝ)) *
      Polynomial.aeval psW (Polynomial.derivative (psYpoly N))) * pssq +
    (-Polynomial.aeval psW (Polynomial.derivative (psYpoly N))) * psBCOMB +
    (Polynomial.aeval psW (Polynomial.derivative (psYpoly N))) * hC14 +
    (PowerSeries.C (2 : ℝ)) * psMapped N +
    (psY N) * psB2C +
    ((Polynomial.aeval psW (Polynomial.derivative (psYpoly N))) *
      PowerSeries.C (2 : ℝ) * psW) * psC2

theorem psConstCoeff (N : ℕ) : PowerSeries.constantCoeff (psG N) = 0 := by
  have hs : PowerSeries.constantCoeff
      (psE - psEb) = 0 := by
    rw [map_sub, PowerSeries.constantCoeff_exp]
    have h1 : PowerSeries.constantCoeff (psEb) = 1 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff]
      exact coeff0_rescale_neg_exp
    rw [h1, sub_self]
  have h2 : PowerSeries.constantCoeff (PowerSeries.C (2 : ℝ) * PowerSeries.X) = 0 := by
    rw [map_mul, PowerSeries.constantCoeff_X, mul_zero]
  unfold psG
  rw [map_sub, map_mul, hs, zero_mul, h2, sub_self]

theorem psDvd (N : ℕ) : PowerSeries.X ^ (2 * N + 3) ∣ psG N := by
  have hD : PowerSeries.X ^ (2 * N + 2) ∣ PowerSeries.derivative (psG N) := by
    rw [psDeriv N]
    have hw : PowerSeries.X ^ (2 * N + 2) ∣ psW ^ (N + 1) := by
      have h := psW_pow_dvd (N + 1)
      have e2 : 2 * (N + 1) = 2 * N + 2 := by ring
      rwa [e2] at h
    exact Dvd.dvd.mul_left hw _
  have h0 := psConstCoeff N
  have h := x_pow_succ_dvd_of_derivative h0 hD
  have e : 2 * N + 2 + 1 = 2 * N + 3 := by omega
  rwa [e] at h

theorem hcb (n : ℕ) : (1 / (((2 * n + 1 : ℕ)) : ℝ)) * psBeta n = psC n := by
  have hF1 : ((((2 * n + 1 : ℕ))) : ℝ) ≠ 0 := by
    apply Nat.cast_ne_zero.mpr
    omega
  have hF2 : ((2 * n).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  unfold psBeta psC
  rw [Nat.factorial_succ]
  push_cast
  field_simp

theorem hYbridge (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), (psC n) • psW ^ n) = psY N := by
  unfold psY psYpoly
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [map_mul, Polynomial.aeval_C, PowerSeries.algebraMap_eq, Polynomial.aeval_X_pow,
    Algebra.smul_def, PowerSeries.algebraMap_eq]

theorem psAct_sub (M : ℕ) (f g : PowerSeries ℝ) (phi : ℝ[X]) :
    psAct M (f - g) phi = psAct M f phi - psAct M g phi := by
  unfold psAct
  rw [map_sub, map_sub, LinearMap.sub_apply]

theorem minus_identity (phi : ℝ[X]) :
    chapter5PolynomialShift 1 (chapter5Entry2MinusSolution phi) -
      chapter5PolynomialShift (-1) (chapter5Entry2MinusSolution phi) =
      Polynomial.C 2 * phi.derivative := by
  have hM : phi.natDegree < phi.natDegree + 1 := Nat.lt_succ_self _
  have hN2 : phi.natDegree < 2 * (phi.natDegree / 2) + 3 := by omega
  have hMinus : chapter5Entry2MinusSolution phi =
      psAct (phi.natDegree + 1)
        (∑ n ∈ Finset.range (phi.natDegree / 2 + 1), (psC n) • psW ^ n) phi := by
    unfold chapter5Entry2MinusSolution
    rw [psAct_sum, LinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro n hn
    rw [← Polynomial.smul_eq_C_mul, entry2F_eq_smul_psAct phi n _ hM, ← mul_smul,
      hcb n, ← LinearMap.smul_apply, ← psAct_smul]
  have hMd : (chapter5Entry2MinusSolution phi).natDegree < phi.natDegree + 1 := by
    rw [hMinus]
    exact lt_of_le_of_lt (psAct_natDegree_le _ _ _) hM
  have sh1 : chapter5PolynomialShift (1 : ℝ) (chapter5Entry2MinusSolution phi) =
      psAct (phi.natDegree + 1) (psE *
        (∑ n ∈ Finset.range (phi.natDegree / 2 + 1), (psC n) • psW ^ n)) phi := by
    have t1 : chapter5PolynomialShift (1 : ℝ) (chapter5Entry2MinusSolution phi) =
        psAct (phi.natDegree + 1) (PowerSeries.rescale 1 (psE))
          (chapter5Entry2MinusSolution phi) :=
      ((Polynomial.taylor_apply _ _).trans rfl).symm.trans (taylor_eq_psAct _ 1 _ hMd)
    rw [t1, hMinus, ← psAct_mul _ _ _ phi hM, rescale_one_exp]
  have sh2 : chapter5PolynomialShift (-1 : ℝ) (chapter5Entry2MinusSolution phi) =
      psAct (phi.natDegree + 1) (psEb *
        (∑ n ∈ Finset.range (phi.natDegree / 2 + 1), (psC n) • psW ^ n)) phi := by
    have t2 : chapter5PolynomialShift (-1 : ℝ) (chapter5Entry2MinusSolution phi) =
        psAct (phi.natDegree + 1) (psEb)
          (chapter5Entry2MinusSolution phi) :=
      ((Polynomial.taylor_apply _ _).trans rfl).symm.trans (taylor_eq_psAct _ (-1) _ hMd)
    rw [t2, hMinus, ← psAct_mul _ _ _ phi hM]
  have hkill : psAct (phi.natDegree + 1) (psG (phi.natDegree / 2)) phi = 0 :=
    psAct_eq_zero_of_X_pow_dvd _ _ _ (psDvd _) hN2
  have hC2X : psAct (phi.natDegree + 1)
      (PowerSeries.C (2 : ℝ) * PowerSeries.X) phi = Polynomial.C 2 * phi.derivative := by
    have e1 : psAct (phi.natDegree + 1)
        (PowerSeries.C (2 : ℝ) * PowerSeries.X) phi =
        psAct (phi.natDegree + 1) (PowerSeries.C (2 : ℝ))
          (psAct (phi.natDegree + 1) PowerSeries.X phi) :=
      psAct_mul _ _ _ phi hM
    have hDd : (phi.derivative).natDegree < phi.natDegree + 1 :=
      lt_of_le_of_lt (Polynomial.natDegree_derivative_le _) (by omega)
    rw [e1, psAct_X_pow _ _ hM, psAct_C _ _ _ hDd, Polynomial.smul_eq_C_mul]
  have hSY : (psE - psEb) *
      (∑ n ∈ Finset.range (phi.natDegree / 2 + 1), (psC n) • psW ^ n) =
      psG (phi.natDegree / 2) + PowerSeries.C (2 : ℝ) * PowerSeries.X := by
    rw [hYbridge]
    unfold psG
    rw [sub_add_cancel]
  rw [sh1, sh2, ← psAct_sub, ← sub_mul, hSY, psAct_add, LinearMap.add_apply, hkill, hC2X,
    zero_add]

theorem hpb (n : ℕ) : ((Nat.choose (2 * n) n : ℝ) / (2 : ℝ) ^ n) * psBeta n = 1 := by
  have key : ((Nat.choose (2 * n) n : ℝ)) * ((n.factorial : ℝ) ^ 2) =
      ((2 * n).factorial : ℝ) := by
    have h := Nat.add_choose_mul_factorial_mul_factorial n n
    have h2 : n + n = 2 * n := by ring
    rw [h2] at h
    rw [sq, ← mul_assoc]
    exact_mod_cast h
  have h2n : (2 : ℝ) ^ n ≠ 0 := by positivity
  have hF : ((2 * n).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  unfold psBeta
  field_simp
  linear_combination key

theorem plus_identity (phi : ℝ[X]) :
    chapter5PolynomialShift 1 (chapter5Entry2PlusSolution phi) +
      chapter5PolynomialShift (-1) (chapter5Entry2PlusSolution phi) =
      Polynomial.C 2 * phi := by
  have hM : phi.natDegree < phi.natDegree + 1 := Nat.lt_succ_self _
  have hN2 : phi.natDegree < 2 * (phi.natDegree / 2) + 2 := by omega
  have hPlus : chapter5Entry2PlusSolution phi =
      psAct (phi.natDegree + 1)
        (∑ n ∈ Finset.range (phi.natDegree / 2 + 1), psW ^ n) phi := by
    unfold chapter5Entry2PlusSolution
    rw [psAct_sum, LinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro n hn
    rw [← Polynomial.smul_eq_C_mul, entry2F_eq_smul_psAct phi n _ hM, ← mul_smul,
      hpb n, one_smul]
  have hMd : (chapter5Entry2PlusSolution phi).natDegree < phi.natDegree + 1 := by
    rw [hPlus]
    exact lt_of_le_of_lt (psAct_natDegree_le _ _ _) hM
  have sh1 : chapter5PolynomialShift (1 : ℝ) (chapter5Entry2PlusSolution phi) =
      psAct (phi.natDegree + 1) (psE *
        (∑ n ∈ Finset.range (phi.natDegree / 2 + 1), psW ^ n)) phi := by
    have t1 : chapter5PolynomialShift (1 : ℝ) (chapter5Entry2PlusSolution phi) =
        psAct (phi.natDegree + 1) (PowerSeries.rescale 1 (psE))
          (chapter5Entry2PlusSolution phi) :=
      ((Polynomial.taylor_apply _ _).trans rfl).symm.trans (taylor_eq_psAct _ 1 _ hMd)
    rw [t1, hPlus, ← psAct_mul _ _ _ phi hM, rescale_one_exp]
  have sh2 : chapter5PolynomialShift (-1 : ℝ) (chapter5Entry2PlusSolution phi) =
      psAct (phi.natDegree + 1) (psEb *
        (∑ n ∈ Finset.range (phi.natDegree / 2 + 1), psW ^ n)) phi := by
    have t2 : chapter5PolynomialShift (-1 : ℝ) (chapter5Entry2PlusSolution phi) =
        psAct (phi.natDegree + 1) (psEb)
          (chapter5Entry2PlusSolution phi) :=
      ((Polynomial.taylor_apply _ _).trans rfl).symm.trans (taylor_eq_psAct _ (-1) _ hMd)
    rw [t2, hPlus, ← psAct_mul _ _ _ phi hM]
  have geom : (1 - psW) * (∑ n ∈ Finset.range (phi.natDegree / 2 + 1), psW ^ n) =
      1 - psW ^ (phi.natDegree / 2 + 1) := by
    have h := mul_geom_sum psW (phi.natDegree / 2 + 1)
    linear_combination -h
  have hEE : (psE + psEb) *
      (∑ n ∈ Finset.range (phi.natDegree / 2 + 1), psW ^ n) =
      2 - 2 * psW ^ (phi.natDegree / 2 + 1) := by
    rw [psB2, mul_assoc, geom, mul_sub, mul_one]
  have hkill2 : psAct (phi.natDegree + 1) (psW ^ (phi.natDegree / 2 + 1)) phi = 0 :=
    psAct_eq_zero_of_X_pow_dvd _ _ _ (psW_pow_dvd _) hN2
  have h2phi : psAct (phi.natDegree + 1) (2 : PowerSeries ℝ) phi = (2 : ℝ) • phi := by
    rw [psC2]
    exact psAct_C _ 2 _ hM
  have h2w : psAct (phi.natDegree + 1)
      ((2 : PowerSeries ℝ) * psW ^ (phi.natDegree / 2 + 1)) phi = 0 := by
    have e : (2 : PowerSeries ℝ) * psW ^ (phi.natDegree / 2 + 1) =
        (2 : ℝ) • psW ^ (phi.natDegree / 2 + 1) := by
      rw [Algebra.smul_def, PowerSeries.algebraMap_eq, psC2]
    rw [e, psAct_smul, LinearMap.smul_apply, hkill2, smul_zero]
  rw [sh1, sh2, ← LinearMap.add_apply, ← psAct_add, ← add_mul, hEE, psAct_sub, h2phi,
    h2w, sub_zero, Polynomial.smul_eq_C_mul]

/-- Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 5,
Entry 2(i), pp. 111–112.

Proves `Wanted` entry `ramanujan_part1_ch5_entry2i_euleriangf`.
-/
theorem ramanujan_part1_ch5_entry2i_euleriangf (phi : ℝ[X]) :
    (∀ n : ℕ, phi.natDegree < 2 * n → chapter5Entry2F phi n = 0) ∧
      chapter5PolynomialShift 1 (chapter5Entry2MinusSolution phi) -
          chapter5PolynomialShift (-1) (chapter5Entry2MinusSolution phi) =
        Polynomial.C 2 * phi.derivative ∧
      chapter5PolynomialShift 1 (chapter5Entry2PlusSolution phi) +
          chapter5PolynomialShift (-1) (chapter5Entry2PlusSolution phi) =
        Polynomial.C 2 * phi := by
  exact ⟨entry2F_eq_zero_of_natDegree_lt phi, minus_identity phi, plus_identity phi⟩

end
end Entry2iEuleriangf
end Ramanujan.Part1Ch5
end
