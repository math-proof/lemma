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
import Def.Analysis.SpecialFunctions.Part1Ch5Entry2iEuleriangf.Part5
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

theorem arcsin_poly_ode (N : ℕ) :
    (1 - Polynomial.X) * psYpoly N +
      (2 * Polynomial.X - Polynomial.X ^ 2) * Polynomial.derivative (psYpoly N) =
      1 - Polynomial.C (((N + 1 : ℕ) : ℝ) * psC N) * Polynomial.X ^ (N + 1) := by
  induction N with
  | zero =>
    have hc0 : psC 0 = 1 := by unfold psC; norm_num
    simp [psYpoly, hc0]
  | succ N IH =>
    have hys : psYpoly (N + 1) = psYpoly N + Polynomial.C (psC (N + 1)) * Polynomial.X ^
        (N + 1) := by
      simp [psYpoly, Finset.sum_range_succ]
    have hstep := ode_step (psC (N + 1)) N
    have hrec := psC_recurrence N
    have hrecC : Polynomial.C ((2 * N + 3) * psC (N + 1)) =
        Polynomial.C (((N + 1 : ℕ) : ℝ) * psC N) := by rw [hrec]
    have htop : Polynomial.C ((((N + 2 : ℕ)) : ℝ) * psC (N + 1)) =
        Polynomial.C (((N : ℝ) + 2) * psC (N + 1)) := by
      rw [Nat.cast_add, Nat.cast_ofNat]
    have eNN : N + 1 + 1 = N + 2 := rfl
    rw [hys, Polynomial.derivative_add]
    rw [eNN]
    linear_combination IH + hstep + (Polynomial.X ^ (N + 1)) * hrecC +
      (Polynomial.X ^ (N + 2)) * htop

theorem taylor_eq_psAct_rescale_exp_aux (m : ℕ) (h : ℝ) (phi : ℝ[X])
    (hM : phi.natDegree < m + 1) :
    Polynomial.taylor h phi =
      (Polynomial.aeval Polynomial.derivative)
        ((PowerSeries.trunc (m + 1)) (PowerSeries.rescale h (psE))) phi := by
  have stepA : (Polynomial.aeval Polynomial.derivative)
        ((PowerSeries.trunc (m + 1)) (PowerSeries.rescale h (psE))) phi =
      ∑ k ∈ Finset.range (m + 1), h ^ k • Polynomial.hasseDeriv k phi := by
    rw [Polynomial.aeval_eq_sum_range' (PowerSeries.natDegree_trunc_lt _ _),
      LinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro k hk
    have hkm : k < m + 1 := Finset.mem_range.mp hk
    have hck : ((PowerSeries.trunc (m + 1)) (PowerSeries.rescale h (psE))).coeff k =
        h ^ k * (1 / (k.factorial : ℝ)) := by
      rw [PowerSeries.coeff_trunc]
      simp only [hkm, ite_true]
      rw [PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
      simp
    have hfact := Polynomial.factorial_smul_hasseDeriv (R := ℝ) k
    have h2 := congrArg (fun F => F phi) hfact
    rw [LinearMap.smul_apply] at h2
    have hF : ((k.factorial : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have e2 : h ^ k * (1 / (k.factorial : ℝ)) * (k.factorial : ℝ) = h ^ k := by
      field_simp
    rw [LinearMap.smul_apply, Module.End.pow_apply, hck, ← h2, nsmul_eq_mul,
      Polynomial.smul_eq_C_mul, Polynomial.smul_eq_C_mul, ← mul_assoc,
      (map_natCast Polynomial.C (k.factorial)).symm, ← map_mul, e2]
  have stepB : Polynomial.taylor h phi =
      ∑ k ∈ Finset.range (m + 1), h ^ k • Polynomial.hasseDeriv k phi := by
    apply Polynomial.ext
    intro n
    have hdeg : (Polynomial.hasseDeriv n phi).natDegree < m + 1 :=
      lt_of_le_of_lt (le_trans (Polynomial.natDegree_hasseDeriv_le phi n) (Nat.sub_le _ _))
        hM
    rw [Polynomial.taylor_coeff, Polynomial.eval_eq_sum_range' hdeg,
      Polynomial.finsetSum_coeff]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Polynomial.coeff_smul, Polynomial.hasseDeriv_coeff, Polynomial.hasseDeriv_coeff,
      smul_eq_mul]
    have echi : (i + n).choose n = (n + i).choose i := by
      rw [add_comm i n]
      exact Nat.choose_symm_add
    rw [echi]
    ring_nf
  rw [stepB, stepA]

theorem n7_full {A : Type*} [CommRing A] [Algebra ℝ A] (a b : A) (hab : a * b = 1) (n : ℕ) :
    1 + ∑ k ∈ Finset.Icc 1 n,
        (((-1 : ℝ) ^ k * ((n.factorial : ℝ) ^ 2) /
          (((n + k).factorial : ℝ) * ((n - k).factorial : ℝ))) • (a ^ k + b ^ k))
      = (((-1 : ℝ) ^ n * ((n.factorial : ℝ) ^ 2) / ((2 * n).factorial : ℝ)) • (a + b - 2) ^ n) := by
  have e2 : a ^ n * b ^ n = 1 := by rw [← mul_pow, hab, one_pow]
  have hexp := n7_expand a b hab n
  have hsplit := sum_range_two_mul_add_one_eq
    (fun j => ((((-1 : ℝ) ^ n * ((n.factorial : ℝ) ^ 2) / ((2 * n).factorial : ℝ)) *
      (((2 * n).choose j : ℝ)) * (-1 : ℝ) ^ (2 * n - j)) • (a ^ j * b ^ n))) n
  have gup : ∀ k ∈ Finset.Icc 1 n,
      ((((-1 : ℝ) ^ n * ((n.factorial : ℝ) ^ 2) / ((2 * n).factorial : ℝ)) *
        (((2 * n).choose (n + k) : ℝ)) * (-1 : ℝ) ^ (2 * n - (n + k))) • (a ^ (n + k) * b ^ n))
      = (((-1 : ℝ) ^ k * ((n.factorial : ℝ) ^ 2) /
          (((n + k).factorial : ℝ) * ((n - k).factorial : ℝ))) • a ^ k) := by
    intro k hk
    have hkle : k ≤ n := (Finset.mem_Icc.mp hk).2
    have e : a ^ (n + k) * b ^ n = a ^ k := by
      have e3 : a ^ (n + k) = a ^ n * a ^ k := pow_add a n k
      rw [e3, show (a ^ n * a ^ k) * b ^ n = (a ^ n * b ^ n) * a ^ k from by ring, e2,
        one_mul]
    rw [e, scalar_match_upper n k hkle]
  have glo : ∀ k ∈ Finset.Icc 1 n,
      ((((-1 : ℝ) ^ n * ((n.factorial : ℝ) ^ 2) / ((2 * n).factorial : ℝ)) *
        (((2 * n).choose (n - k) : ℝ)) * (-1 : ℝ) ^ (2 * n - (n - k))) • (a ^ (n - k) * b ^ n))
      = (((-1 : ℝ) ^ k * ((n.factorial : ℝ) ^ 2) /
          (((n + k).factorial : ℝ) * ((n - k).factorial : ℝ))) • b ^ k) := by
    intro k hk
    have hkle : k ≤ n := (Finset.mem_Icc.mp hk).2
    have e3 : b ^ n = b ^ (n - k) * b ^ k := by rw [← pow_add, Nat.sub_add_cancel hkle]
    have e4 : a ^ (n - k) * b ^ (n - k) = 1 := by rw [← mul_pow, hab, one_pow]
    have e : a ^ (n - k) * b ^ n = b ^ k := by
      rw [e3, show a ^ (n - k) * (b ^ (n - k) * b ^ k) =
        (a ^ (n - k) * b ^ (n - k)) * b ^ k from by ring, e4, one_mul]
    rw [e, scalar_match_lower n k hkle]
  have gmid : ((((-1 : ℝ) ^ n * ((n.factorial : ℝ) ^ 2) / ((2 * n).factorial : ℝ)) *
        (((2 * n).choose n : ℝ)) * (-1 : ℝ) ^ (2 * n - n)) • (a ^ n * b ^ n)) = 1 := by
    rw [e2, scalar_match_center n, one_smul]
  rw [hexp, hsplit, gmid]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [gup k hk, glo k hk, smul_add]

theorem taylor_eq_psAct (M : ℕ) (h : ℝ) (phi : ℝ[X]) (hM : phi.natDegree < M) :
    Polynomial.taylor h phi = psAct M (PowerSeries.rescale h (psE)) phi := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : M ≠ 0)
  exact taylor_eq_psAct_rescale_exp_aux m h phi hM

theorem psAct_exp_pow_shift (M : ℕ) (k : ℕ) (phi : ℝ[X]) (hM : phi.natDegree < M) :
    psAct M (psE ^ k) phi = chapter5PolynomialShift (k : ℝ) phi := by
  rw [exp_pow_eq_rescale, ← taylor_eq_psAct M _ phi hM]
  exact (Polynomial.taylor_apply _ _).trans rfl

theorem psAct_ebar_pow_shift (M : ℕ) (k : ℕ) (phi : ℝ[X]) (hM : phi.natDegree < M) :
    psAct M (psEb ^ k) phi =
      chapter5PolynomialShift (-(k : ℝ)) phi := by
  rw [rescale_neg_pow, ← taylor_eq_psAct M _ phi hM]
  exact (Polynomial.taylor_apply _ _).trans rfl

end
end Entry2iEuleriangf
end Ramanujan.Part1Ch5
end
