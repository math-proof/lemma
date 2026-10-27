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
import Def.Analysis.SpecialFunctions.Part1Ch5Entry2iEuleriangf.Part3
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

theorem psAct_trunc_aeval (M : ℕ) (p : ℝ[X]) (phi : ℝ[X]) (hM : phi.natDegree < M) :
    (Polynomial.aeval Polynomial.derivative) ((PowerSeries.trunc M) (p : PowerSeries ℝ)) phi =
      (Polynomial.aeval Polynomial.derivative) p phi := by
  apply aeval_derivative_apply_eq_of_sub _ hM
  rw [Polynomial.X_pow_dvd_iff]
  intro d hd
  have h1 : ((PowerSeries.trunc M) (p : PowerSeries ℝ)).coeff d = p.coeff d := by
    simp [PowerSeries.coeff_trunc, Polynomial.coeff_coe, hd]
  have h2 : ((PowerSeries.trunc M) (p : PowerSeries ℝ) - p).coeff d =
      ((PowerSeries.trunc M) (p : PowerSeries ℝ)).coeff d - p.coeff d := by simp
  rw [h2, h1, sub_self]

theorem psAct_add (M : ℕ) (f g : PowerSeries ℝ) :
    psAct M (f + g) = psAct M f + psAct M g := by
  unfold psAct
  rw [map_add, map_add]

theorem psAct_smul (M : ℕ) (c : ℝ) (f : PowerSeries ℝ) :
    psAct M (c • f) = c • psAct M f := by
  unfold psAct
  rw [map_smul, map_smul]

theorem psAct_sum (M : ℕ) {ι : Type*} (s : Finset ι) (F : ι → PowerSeries ℝ) :
    psAct M (∑ i ∈ s, F i) = ∑ i ∈ s, psAct M (F i) := by
  unfold psAct
  rw [map_sum, map_sum]

theorem psAct_one (M : ℕ) (phi : ℝ[X]) (hM : phi.natDegree < M) :
    psAct M 1 phi = phi := by
  unfold psAct
  rw [← Polynomial.coe_one, psAct_trunc_aeval M 1 phi hM, map_one, Module.End.one_apply]

theorem psAct_X_pow (M : ℕ) (phi : ℝ[X]) (hM : phi.natDegree < M) :
    psAct M PowerSeries.X phi = Polynomial.derivative phi := by
  unfold psAct
  rw [← Polynomial.coe_X, psAct_trunc_aeval M Polynomial.X phi hM, Polynomial.aeval_X]

theorem psAct_C (M : ℕ) (c : ℝ) (phi : ℝ[X]) (hM : phi.natDegree < M) :
    psAct M (PowerSeries.C c) phi = c • phi := by
  unfold psAct
  rw [← Polynomial.coe_C, psAct_trunc_aeval M (Polynomial.C c) phi hM, Polynomial.aeval_C,
    Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply]

theorem psAct_natDegree_le (M : ℕ) (f : PowerSeries ℝ) (phi : ℝ[X]) :
    (psAct M f phi).natDegree ≤ phi.natDegree := by
  unfold psAct
  exact natDegree_aeval_derivative_apply_le _ _

theorem psAct_mul (M : ℕ) (f g : PowerSeries ℝ) (phi : ℝ[X]) (hM : phi.natDegree < M) :
    psAct M (f * g) phi = psAct M f (psAct M g phi) := by
  have htr : (PowerSeries.trunc M) (f * g) =
      (PowerSeries.trunc M) (((PowerSeries.trunc M f * PowerSeries.trunc M g : ℝ[X]) :
        PowerSeries ℝ)) := by
    rw [Polynomial.coe_mul, PowerSeries.trunc_trunc_mul_trunc]
  unfold psAct
  rw [htr, psAct_trunc_aeval M _ phi hM, map_mul, Module.End.mul_apply]

theorem psAct_eq_zero_of_X_pow_dvd (M : ℕ) (f : PowerSeries ℝ) (phi : ℝ[X]) {m : ℕ}
    (hdvd : PowerSeries.X ^ m ∣ f) (hlt : phi.natDegree < m) :
    psAct M f phi = 0 := by
  apply aeval_derivative_apply_eq_zero _ hlt
  rw [Polynomial.X_pow_dvd_iff]
  intro d hd
  have h1 : PowerSeries.coeff d f = 0 := (PowerSeries.X_pow_dvd_iff.mp hdvd) d hd
  rw [PowerSeries.coeff_trunc]
  split_ifs with hM'
  · exact h1
  · rfl

theorem coeff_exp_real (n : ℕ) :
    PowerSeries.coeff n (psE) = 1 / (n.factorial : ℝ) := by
  rw [PowerSeries.coeff_exp]
  simp

theorem exp_mul_rescale_neg_eq_one :
    psE * psEb = 1 :=
  PowerSeries.exp_mul_exp_neg_eq_one

theorem exp_pow_eq_rescale (k : ℕ) :
    psE ^ k = PowerSeries.rescale (k : ℝ) (psE) :=
  PowerSeries.exp_pow_eq_rescale_exp k

theorem rescale_neg_pow (k : ℕ) :
    psEb ^ k =
      PowerSeries.rescale (-(k : ℝ)) (psE) := by
  rw [← map_pow, exp_pow_eq_rescale, PowerSeries.rescale_rescale]
  congr 1
  ring_nf

theorem rescale_one_exp :
    PowerSeries.rescale (1 : ℝ) (psE) = psE := by
  rw [PowerSeries.rescale_one]
  rfl

theorem derivative_rescale_neg_exp :
    PowerSeries.derivative (psEb) =
      -(psEb) := by
  apply PowerSeries.ext_iff.mpr
  intro n
  rw [map_neg]
  have h1 : PowerSeries.coeff n (PowerSeries.derivative (psEb))
      = (-1 : ℝ) ^ (n + 1) * (1 / (((n + 1).factorial : ℝ))) * ((n : ℝ) + 1) := by
    rw [PowerSeries.coeff_derivative, PowerSeries.coeff_rescale, coeff_exp_real]
  have h2 : PowerSeries.coeff n (psEb)
      = (-1 : ℝ) ^ n * (1 / ((n.factorial : ℝ))) := by
    rw [PowerSeries.coeff_rescale, coeff_exp_real]
  rw [h1, h2]
  have hF : ((n + 1).factorial : ℝ) = ((n : ℝ) + 1) * (n.factorial : ℝ) := by
    push_cast [Nat.factorial_succ]
    ring
  have hFne : ((n.factorial : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hneg : (-1 : ℝ) ^ (n + 1) = -(-1 : ℝ) ^ n := by
    rw [pow_succ, mul_neg, mul_one]
  rw [hneg, hF]
  field_simp

theorem coeff0_exp : PowerSeries.coeff 0 (psE) = 1 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.constantCoeff_exp]

theorem coeff1_exp : PowerSeries.coeff 1 (psE) = 1 := by
  rw [coeff_exp_real]
  norm_num

theorem coeff0_rescale_neg_exp :
    PowerSeries.coeff 0 (psEb) = 1 := by
  rw [PowerSeries.coeff_rescale, coeff0_exp]
  norm_num

theorem coeff1_rescale_neg_exp :
    PowerSeries.coeff 1 (psEb) = -1 := by
  rw [PowerSeries.coeff_rescale, coeff1_exp]
  norm_num

theorem coeff0_two : PowerSeries.coeff 0 (2 : PowerSeries ℝ) = 2 := by
  rw [show (2 : PowerSeries ℝ) = PowerSeries.C 2 from rfl, PowerSeries.coeff_C]
  norm_num

theorem coeff1_two : PowerSeries.coeff 1 (2 : PowerSeries ℝ) = 0 := by
  rw [show (2 : PowerSeries ℝ) = PowerSeries.C 2 from rfl, PowerSeries.coeff_C]
  norm_num

theorem exp_add_rescale_sub_two :
    PowerSeries.X ^ 2 ∣ (psE + psEb - 2) := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro m hm
  interval_cases m
  · rw [map_sub, map_add, coeff0_exp, coeff0_rescale_neg_exp, coeff0_two]
    norm_num
  · rw [map_sub, map_add, coeff1_exp, coeff1_rescale_neg_exp, coeff1_two]
    norm_num

end
end Entry2iEuleriangf
end Ramanujan.Part1Ch5
end
