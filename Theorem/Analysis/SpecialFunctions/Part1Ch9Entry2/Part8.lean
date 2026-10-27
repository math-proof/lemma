/-
Author: @akiezun, Avocado
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Basic
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Instances.AddCircle.Defs
import Def.Analysis.SpecialFunctions.Part1Ch9Entry2.Part8
/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace Ramanujan.Part1Ch9

namespace Entry2

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Filter Finset Complex Topology MeasureTheory

noncomputable section

theorem entry2Q_two (a : ℝ)
    (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ)) : entry2Q a 2 := by
  intro x hx
  constructor
  · intro _
    exact hasSum_Q2 a ha x hx
  · intro ho
    obtain ⟨m, hm⟩ := ho
    omega

theorem hasDerivAt_cos_div (u : ℝ) (hu : u ≠ 0) (r : ℕ) (hr : 1 ≤ r)
    (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.cos (u * y) / u ^ r)
      (-(Real.sin (u * x) / u ^ (r - 1))) x := by
  have hlin : HasDerivAt (fun y : ℝ => u * y) u x := by
    simpa using (hasDerivAt_id' x).const_mul u
  have hcos : HasDerivAt (fun y : ℝ => Real.cos (u * y))
      (-Real.sin (u * x) * u) x :=
    (Real.hasDerivAt_cos (u * x)).comp x hlin
  have hdiv := hcos.div_const (u ^ r)
  have hrw : r = 1 + (r - 1) := by omega
  have hpow : u ^ r = u * u ^ (r - 1) := by
    conv_lhs => rw [hrw]
    rw [pow_add, pow_one]
  have heq : (-Real.sin (u * x) * u) / u ^ r
      = -(Real.sin (u * x) / u ^ (r - 1)) := by
    rw [hpow]
    have h1 : u ^ (r - 1) ≠ 0 := pow_ne_zero _ hu
    have hprod : u * u ^ (r - 1) ≠ 0 := mul_ne_zero hu h1
    field_simp
  rw [heq] at hdiv
  exact hdiv

theorem hasDerivAt_sin_div (u : ℝ) (hu : u ≠ 0) (r : ℕ) (hr : 1 ≤ r)
    (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.sin (u * y) / u ^ r)
      (Real.cos (u * x) / u ^ (r - 1)) x := by
  have hlin : HasDerivAt (fun y : ℝ => u * y) u x := by
    simpa using (hasDerivAt_id' x).const_mul u
  have hsin : HasDerivAt (fun y : ℝ => Real.sin (u * y))
      (Real.cos (u * x) * u) x :=
    (Real.hasDerivAt_sin (u * x)).comp x hlin
  have hdiv := hsin.div_const (u ^ r)
  have hrw : r = 1 + (r - 1) := by omega
  have hpow : u ^ r = u * u ^ (r - 1) := by
    conv_lhs => rw [hrw]
    rw [pow_add, pow_one]
  have heq : (Real.cos (u * x) * u) / u ^ r
      = Real.cos (u * x) / u ^ (r - 1) := by
    rw [hpow]
    have h1 : u ^ (r - 1) ≠ 0 := pow_ne_zero _ hu
    have hprod : u * u ^ (r - 1) ≠ 0 := mul_ne_zero hu h1
    field_simp
  rw [heq] at hdiv
  exact hdiv

theorem hasDerivAt_cosineTerm (r : ℕ) (a : ℝ)
    (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ)) (hr : 1 ≤ r) (k : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => chapter9Entry2CosineTerm r a y k)
      (-(chapter9Entry2SineTerm (r - 1) a x k)) x := by
  have hp : (((2 * k + 1 : ℕ) : ℝ) - a) ≠ 0 := sub_ne_zero_of_ha a ha k
  have hq : (((2 * k + 1 : ℕ) : ℝ) + a) ≠ 0 := add_ne_zero_of_ha a ha k
  have h1 := hasDerivAt_cos_div _ hp r hr x
  have h2 := hasDerivAt_cos_div _ hq r hr x
  have hsum := h1.fun_add h2
  have hderiv : (-(Real.sin (((((2 * k + 1 : ℕ)) : ℝ) - a) * x) /
          ((((2 * k + 1 : ℕ)) : ℝ) - a) ^ (r - 1)) +
        -(Real.sin (((((2 * k + 1 : ℕ)) : ℝ) + a) * x) /
          ((((2 * k + 1 : ℕ)) : ℝ) + a) ^ (r - 1)))
      = -(chapter9Entry2SineTerm (r - 1) a x k) := by
    unfold chapter9Entry2SineTerm
    ring
  rw [hderiv] at hsum
  exact hsum

theorem hasDerivAt_sineTerm (r : ℕ) (a : ℝ)
    (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ)) (hr : 1 ≤ r) (k : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => chapter9Entry2SineTerm r a y k)
      (chapter9Entry2CosineTerm (r - 1) a x k) x := by
  have hp : (((2 * k + 1 : ℕ) : ℝ) - a) ≠ 0 := sub_ne_zero_of_ha a ha k
  have hq : (((2 * k + 1 : ℕ) : ℝ) + a) ≠ 0 := add_ne_zero_of_ha a ha k
  have h1 := hasDerivAt_sin_div _ hp r hr x
  have h2 := hasDerivAt_sin_div _ hq r hr x
  have hsum := h1.fun_add h2
  have hderiv : (Real.cos (((((2 * k + 1 : ℕ)) : ℝ) - a) * x) /
          ((((2 * k + 1 : ℕ)) : ℝ) - a) ^ (r - 1) +
        Real.cos (((((2 * k + 1 : ℕ)) : ℝ) + a) * x) /
          ((((2 * k + 1 : ℕ)) : ℝ) + a) ^ (r - 1))
      = chapter9Entry2CosineTerm (r - 1) a x k := by
    unfold chapter9Entry2CosineTerm
    ring
  rw [hderiv] at hsum
  exact hsum

theorem hasDerivAt_tsum_cosine (r : ℕ) (a : ℝ)
    (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ)) (hr : 3 ≤ r) (x : ℝ) :
    HasDerivAt (fun y : ℝ => ∑' k, chapter9Entry2CosineTerm r a y k)
      (-(∑' k, chapter9Entry2SineTerm (r - 1) a x k)) x := by
  have hr1 : 1 ≤ r := by omega
  have hr2 : 2 ≤ r - 1 := by omega
  have hu : Summable (chapter9Entry2AbsMajorant (r - 1) a) :=
    summable_absMajorant (r - 1) a hr2
  have hg : ∀ k y, HasDerivAt (fun z : ℝ => chapter9Entry2CosineTerm r a z k)
      (-(chapter9Entry2SineTerm (r - 1) a y k)) y :=
    fun k y => hasDerivAt_cosineTerm r a ha hr1 k y
  have hg' : ∀ k y, ‖-(chapter9Entry2SineTerm (r - 1) a y k)‖ ≤
      chapter9Entry2AbsMajorant (r - 1) a k := by
    intro k y
    rw [norm_neg]
    exact norm_sineTerm_le_absMajorant (r - 1) a y k
  have hg0 : Summable (fun k => chapter9Entry2CosineTerm r a 0 k) :=
    summable_cosineTerm_zero r a (by omega)
  have hneg : (∑' k, -(chapter9Entry2SineTerm (r - 1) a x k))
      = -(∑' k, chapter9Entry2SineTerm (r - 1) a x k) := tsum_neg
  rw [← hneg]
  exact hasDerivAt_tsum (u := chapter9Entry2AbsMajorant (r - 1) a)
    (g := fun k y => chapter9Entry2CosineTerm r a y k)
    (g' := fun k y => -(chapter9Entry2SineTerm (r - 1) a y k)) (y₀ := (0 : ℝ))
    hu hg hg' hg0 x

theorem hasDerivAt_tsum_sine (r : ℕ) (a : ℝ)
    (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ)) (hr : 3 ≤ r) (x : ℝ) :
    HasDerivAt (fun y : ℝ => ∑' k, chapter9Entry2SineTerm r a y k)
      (∑' k, chapter9Entry2CosineTerm (r - 1) a x k) x := by
  have hr1 : 1 ≤ r := by omega
  have hr2 : 2 ≤ r - 1 := by omega
  have hu : Summable (chapter9Entry2AbsMajorant (r - 1) a) :=
    summable_absMajorant (r - 1) a hr2
  have hg : ∀ k y, HasDerivAt (fun z : ℝ => chapter9Entry2SineTerm r a z k)
      (chapter9Entry2CosineTerm (r - 1) a y k) y :=
    fun k y => hasDerivAt_sineTerm r a ha hr1 k y
  have hg' : ∀ k y, ‖chapter9Entry2CosineTerm (r - 1) a y k‖ ≤
      chapter9Entry2AbsMajorant (r - 1) a k :=
    fun k y => norm_cosineTerm_le_absMajorant (r - 1) a y k
  have hg0 : Summable (fun k => chapter9Entry2SineTerm r a 0 k) := by
    have hfun : (fun k => chapter9Entry2SineTerm r a 0 k) = (fun _ => (0 : ℝ)) := by
      funext k
      exact sineTerm_zero_eq r a k
    rw [hfun]
    exact summable_zero
  exact hasDerivAt_tsum (u := chapter9Entry2AbsMajorant (r - 1) a)
    (g := fun k y => chapter9Entry2SineTerm r a y k)
    (g' := fun k y => chapter9Entry2CosineTerm (r - 1) a y k) (y₀ := (0 : ℝ))
    hu hg hg' hg0 x

theorem hasDerivAt_cosSummand (r : ℕ) (a x : ℝ) (k : ℕ) :
    HasDerivAt (entry2CosSummand r a k) (entry2CosSummandDeriv r a x k) x := by
  exact (((hasDerivAt_pow (2 * k) x).const_mul
    ((-1 : ℝ) ^ k * chapter9Entry2Constant (r - 2 * k) a)).div_const
    (((2 * k).factorial : ℕ) : ℝ))

theorem hasDerivAt_sinSummand (r : ℕ) (a x : ℝ) (k : ℕ) :
    HasDerivAt (entry2SinSummand r a k) (entry2SinSummandDeriv r a x k) x := by
  exact (((hasDerivAt_pow (2 * k + 1) x).const_mul
    ((-1 : ℝ) ^ k * chapter9Entry2Constant (r - 1 - 2 * k) a)).div_const
    (((2 * k + 1).factorial : ℕ) : ℝ))

theorem hasDerivAt_cosPi (r : ℕ) (x : ℝ) :
    HasDerivAt (entry2CosPi r) (entry2CosPiDeriv r x) x := by
  exact (((hasDerivAt_pow (r - 1) x).const_mul
    ((-1 : ℝ) ^ (r / 2) * Real.pi)).div_const
    (2 * ((((r - 1).factorial : ℕ)) : ℝ)))

theorem hasDerivAt_sinPi (r : ℕ) (x : ℝ) :
    HasDerivAt (entry2SinPi r) (entry2SinPiDeriv r x) x := by
  exact (((hasDerivAt_pow (r - 1) x).const_mul
    ((-1 : ℝ) ^ ((r - 1) / 2) * Real.pi)).div_const
    (2 * ((((r - 1).factorial : ℕ)) : ℝ)))

theorem cosDeriv_term_eq (r : ℕ) (a x : ℝ) (j : ℕ) :
    entry2CosSummandDeriv r a x (j + 1)
      = -entry2SinSummand (r - 1) a j x := by
  unfold entry2CosSummandDeriv entry2SinSummand
  have hC : r - 2 * (j + 1) = r - 1 - 1 - 2 * j := by omega
  have he' : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
  have hF : (2 * (j + 1)).factorial = (2 * (j + 1)) * (2 * j + 1).factorial := by
    have hN : 2 * (j + 1) = (2 * j + 1) + 1 := by omega
    conv_lhs => rw [hN]
    rw [Nat.factorial_succ, ← hN]
  have hF' : ((((2 * (j + 1)).factorial : ℕ)) : ℝ)
      = (((2 * (j + 1) : ℕ)) : ℝ) * ((((2 * j + 1).factorial : ℕ)) : ℝ) := by
    exact_mod_cast hF
  rw [hC, he', hF', pow_succ (-1 : ℝ) j]
  have hN' : (((2 * (j + 1) : ℕ)) : ℝ) ≠ 0 := by
    have hne : 2 * (j + 1) ≠ 0 := by omega
    exact_mod_cast hne
  have hF2 : ((((2 * j + 1).factorial : ℕ)) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero _
  have hprod : (((2 * (j + 1) : ℕ)) : ℝ)
      * ((((2 * j + 1).factorial : ℕ)) : ℝ) ≠ 0 := mul_ne_zero hN' hF2
  field_simp

theorem cosPiDeriv_eq (r : ℕ) (x : ℝ) (hr : 2 ≤ r) (he : Even r) :
    entry2CosPiDeriv r x
      = -((-1 : ℝ) ^ ((r - 1 - 1) / 2) * Real.pi * x ^ (r - 1 - 1) /
        (2 * ((((r - 1 - 1).factorial : ℕ)) : ℝ))) := by
  unfold entry2CosPiDeriv
  have hsr : (r - 1 - 1) / 2 + 1 = r / 2 := by
    obtain ⟨m, hm⟩ := he
    omega
  have hfac : (r - 1).factorial = (r - 1) * (r - 1 - 1).factorial := by
    have h1 : r - 1 = (r - 1 - 1) + 1 := by omega
    conv_lhs => rw [h1]
    rw [Nat.factorial_succ, ← h1]
  have hfac' : ((((r - 1).factorial : ℕ)) : ℝ)
      = ((((r - 1 : ℕ))) : ℝ) * ((((r - 1 - 1).factorial : ℕ)) : ℝ) := by
    exact_mod_cast hfac
  rw [hfac', ← hsr, pow_succ]
  have h1 : ((((r - 1 : ℕ))) : ℝ) ≠ 0 := by
    have hne : r - 1 ≠ 0 := by omega
    exact_mod_cast hne
  have h2 : ((((r - 1 - 1).factorial : ℕ)) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero _
  have hprod : (2 : ℝ) * (((((r - 1 : ℕ))) : ℝ)
      * ((((r - 1 - 1).factorial : ℕ)) : ℝ)) ≠ 0 :=
    mul_ne_zero (by norm_num) (mul_ne_zero h1 h2)
  have hprod2 : (2 : ℝ) * ((((r - 1 - 1).factorial : ℕ)) : ℝ) ≠ 0 :=
    mul_ne_zero (by norm_num) h2
  field_simp

theorem hasDerivAt_Pcos (r : ℕ) (a x : ℝ) (hr : 2 ≤ r) (he : Even r) :
    HasDerivAt (entry2Pcos r a) (-(entry2Psin (r - 1) a x)) x := by
  have hsum : HasDerivAt
      (fun y : ℝ => ∑ k ∈ range (r / 2), entry2CosSummand r a k y)
      (∑ k ∈ range (r / 2), entry2CosSummandDeriv r a x k) x :=
    HasDerivAt.fun_sum (A := entry2CosSummand r a) (A' := entry2CosSummandDeriv r a x)
      (fun k _ => hasDerivAt_cosSummand r a x k)
  have hpi : HasDerivAt (entry2CosPi r) (entry2CosPiDeriv r x) x :=
    hasDerivAt_cosPi r x
  have htot := hsum.fun_add hpi
  have hval : (∑ k ∈ range (r / 2), entry2CosSummandDeriv r a x k)
      + entry2CosPiDeriv r x = -(entry2Psin (r - 1) a x) := by
    have hsum_eq : (∑ k ∈ range (r / 2), entry2CosSummandDeriv r a x k)
        = -(∑ k ∈ range ((r - 1 - 1) / 2), entry2SinSummand (r - 1) a k x) := by
      have hs1 : r / 2 = (r - 1 - 1) / 2 + 1 := by
        obtain ⟨m, hm⟩ := he
        omega
      conv_lhs => rw [hs1]
      simp only [Finset.sum_range_succ']
      have hf0 : entry2CosSummandDeriv r a x 0 = 0 := by
        unfold entry2CosSummandDeriv
        simp only [mul_zero, Nat.cast_zero, zero_mul, zero_div]
      rw [hf0, add_zero]
      have hneg : -(∑ k ∈ range ((r - 1 - 1) / 2),
            entry2SinSummand (r - 1) a k x)
          = ∑ k ∈ range ((r - 1 - 1) / 2),
            -entry2SinSummand (r - 1) a k x :=
        (Finset.sum_neg_distrib _).symm
      rw [hneg]
      apply Finset.sum_congr rfl
      intro j hj
      exact cosDeriv_term_eq r a x j
    have hpi_eq := cosPiDeriv_eq r x hr he
    rw [hsum_eq, hpi_eq]
    unfold entry2Psin entry2SinSummand entry2SinPi
    ring
  rw [hval] at htot
  exact htot

theorem sinDeriv_term_eq (r : ℕ) (a x : ℝ) (k : ℕ) :
    entry2SinSummandDeriv r a x k
      = entry2CosSummand (r - 1) a k x := by
  unfold entry2SinSummandDeriv entry2CosSummand
  have he' : 2 * k + 1 - 1 = 2 * k := by omega
  have hF : (2 * k + 1).factorial = (2 * k + 1) * (2 * k).factorial :=
    Nat.factorial_succ (2 * k)
  have hF' : ((((2 * k + 1).factorial : ℕ)) : ℝ)
      = ((((2 * k + 1 : ℕ))) : ℝ) * ((((2 * k).factorial : ℕ)) : ℝ) := by
    exact_mod_cast hF
  rw [he', hF']
  have hN' : ((((2 * k + 1 : ℕ))) : ℝ) ≠ 0 := by
    have hne : 2 * k + 1 ≠ 0 := by omega
    exact_mod_cast hne
  have hF2 : ((((2 * k).factorial : ℕ)) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero _
  have hprod : ((((2 * k + 1 : ℕ))) : ℝ)
      * ((((2 * k).factorial : ℕ)) : ℝ) ≠ 0 := mul_ne_zero hN' hF2
  field_simp

theorem sinPiDeriv_eq (r : ℕ) (x : ℝ) (hr : 2 ≤ r) :
    entry2SinPiDeriv r x
      = (-1 : ℝ) ^ ((r - 1) / 2) * Real.pi * x ^ ((r - 1) - 1) /
        (2 * ((((r - 1 - 1).factorial : ℕ)) : ℝ)) := by
  unfold entry2SinPiDeriv
  have hfac : (r - 1).factorial = (r - 1) * (r - 1 - 1).factorial := by
    have h1 : r - 1 = (r - 1 - 1) + 1 := by omega
    conv_lhs => rw [h1]
    rw [Nat.factorial_succ, ← h1]
  have hfac' : ((((r - 1).factorial : ℕ)) : ℝ)
      = ((((r - 1 : ℕ))) : ℝ) * ((((r - 1 - 1).factorial : ℕ)) : ℝ) := by
    exact_mod_cast hfac
  rw [hfac']
  have h1 : ((((r - 1 : ℕ))) : ℝ) ≠ 0 := by
    have hne : r - 1 ≠ 0 := by omega
    exact_mod_cast hne
  have h2 : ((((r - 1 - 1).factorial : ℕ)) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero _
  have hprod : (2 : ℝ) * (((((r - 1 : ℕ))) : ℝ)
      * ((((r - 1 - 1).factorial : ℕ)) : ℝ)) ≠ 0 :=
    mul_ne_zero (by norm_num) (mul_ne_zero h1 h2)
  have hprod2 : (2 : ℝ) * ((((r - 1 - 1).factorial : ℕ)) : ℝ) ≠ 0 :=
    mul_ne_zero (by norm_num) h2
  field_simp

theorem hasDerivAt_Psin (r : ℕ) (a x : ℝ) (hr : 2 ≤ r) :
    HasDerivAt (entry2Psin r a) (entry2Pcos (r - 1) a x) x := by
  have hsum : HasDerivAt
      (fun y : ℝ => ∑ k ∈ range ((r - 1) / 2), entry2SinSummand r a k y)
      (∑ k ∈ range ((r - 1) / 2), entry2SinSummandDeriv r a x k) x :=
    HasDerivAt.fun_sum (A := entry2SinSummand r a) (A' := entry2SinSummandDeriv r a x)
      (fun k _ => hasDerivAt_sinSummand r a x k)
  have hpi : HasDerivAt (entry2SinPi r) (entry2SinPiDeriv r x) x :=
    hasDerivAt_sinPi r x
  have htot := hsum.fun_add hpi
  have hval : (∑ k ∈ range ((r - 1) / 2), entry2SinSummandDeriv r a x k)
      + entry2SinPiDeriv r x = entry2Pcos (r - 1) a x := by
    have hsum_eq : (∑ k ∈ range ((r - 1) / 2), entry2SinSummandDeriv r a x k)
        = ∑ k ∈ range ((r - 1) / 2), entry2CosSummand (r - 1) a k x := by
      apply Finset.sum_congr rfl
      intro k hk
      exact sinDeriv_term_eq r a x k
    have hpi_eq := sinPiDeriv_eq r x hr
    rw [hsum_eq, hpi_eq]
    unfold entry2Pcos entry2CosSummand entry2CosPi
    ring
  rw [hval] at htot
  exact htot

theorem Pcos_zero (r : ℕ) (a : ℝ) (hr : 2 ≤ r) (he : Even r) :
    entry2Pcos r a 0 = chapter9Entry2Constant r a := by
  have hs : 1 ≤ r / 2 := by
    obtain ⟨m, hm⟩ := he
    omega
  have hsum : (∑ k ∈ range (r / 2), entry2CosSummand r a k 0)
      = entry2CosSummand r a 0 0 := by
    apply Finset.sum_eq_single 0
    · intro k hk hk0
      unfold entry2CosSummand
      have hne : 2 * k ≠ 0 := by omega
      simp only [zero_pow hne, mul_zero, zero_div]
    · intro h0
      simp only [Finset.mem_range, Nat.not_lt] at h0
      have hF : False := by omega
      exact hF.elim
  have hF0 : entry2CosSummand r a 0 0 = chapter9Entry2Constant r a := by
    unfold entry2CosSummand
    simp only [mul_zero, Nat.sub_zero, pow_zero, Nat.factorial_zero, Nat.cast_one,
      one_mul, mul_one, div_one]
  have hpi : entry2CosPi r 0 = 0 := by
    unfold entry2CosPi
    have hne : r - 1 ≠ 0 := by omega
    simp only [zero_pow hne, mul_zero, zero_div]
  unfold entry2Pcos
  rw [hsum, hF0, hpi, add_zero]

theorem Psin_zero (r : ℕ) (a : ℝ) (hr : 2 ≤ r) :
    entry2Psin r a 0 = 0 := by
  have hsum : (∑ k ∈ range ((r - 1) / 2), entry2SinSummand r a k 0) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    unfold entry2SinSummand
    have hne : 2 * k + 1 ≠ 0 := by omega
    simp only [zero_pow hne, mul_zero, zero_div]
  have hpi : entry2SinPi r 0 = 0 := by
    unfold entry2SinPi
    have hne : r - 1 ≠ 0 := by omega
    simp only [zero_pow hne, mul_zero, zero_div]
  unfold entry2Psin
  rw [hsum, hpi, add_zero]

theorem step_cosine (r : ℕ) (a : ℝ)
    (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ)) (hr : 3 ≤ r) (he : Even r)
    (IH : ∀ x ∈ Set.Ico (0 : ℝ) Real.pi,
      HasSum (chapter9Entry2SineTerm (r - 1) a x) (entry2Psin (r - 1) a x))
    (x0 : ℝ) (hx0 : x0 ∈ Set.Ico (0 : ℝ) Real.pi) :
    HasSum (chapter9Entry2CosineTerm r a x0) (entry2Pcos r a x0) := by
  have hr2 : 2 ≤ r := by omega
  have hS : ∀ y : ℝ, HasDerivAt
      (fun z : ℝ => ∑' k, chapter9Entry2CosineTerm r a z k)
      (-(∑' k, chapter9Entry2SineTerm (r - 1) a y k)) y :=
    fun y => hasDerivAt_tsum_cosine r a ha hr y
  have hP : ∀ y : ℝ, HasDerivAt (entry2Pcos r a)
      (-(entry2Psin (r - 1) a y)) y :=
    fun y => hasDerivAt_Pcos r a y hr2 he
  have hD : ∀ y : ℝ, HasDerivAt
      ((fun z : ℝ => ∑' k, chapter9Entry2CosineTerm r a z k) - entry2Pcos r a)
      ((-(∑' k, chapter9Entry2SineTerm (r - 1) a y k))
        - (-(entry2Psin (r - 1) a y))) y :=
    fun y => (hS y).sub (hP y)
  have hcont : ContinuousOn
      ((fun z : ℝ => ∑' k, chapter9Entry2CosineTerm r a z k) - entry2Pcos r a)
      (Set.Icc 0 x0) := by
    have hC : Continuous
        ((fun z : ℝ => ∑' k, chapter9Entry2CosineTerm r a z k) - entry2Pcos r a) :=
      continuous_iff_continuousAt.mpr (fun y => (hD y).continuousAt)
    exact hC.continuousOn
  have hderiv : ∀ y ∈ Set.Ico 0 x0, HasDerivWithinAt
      ((fun z : ℝ => ∑' k, chapter9Entry2CosineTerm r a z k) - entry2Pcos r a)
      0 (Set.Ici y) y := by
    intro y hy
    have hyIco : y ∈ Set.Ico (0 : ℝ) Real.pi := ⟨hy.1, lt_of_lt_of_le hy.2 hx0.2.le⟩
    have hIH := IH y hyIco
    have htsum : (∑' k, chapter9Entry2SineTerm (r - 1) a y k)
        = entry2Psin (r - 1) a y := hIH.tsum_eq
    have h0 : ((-(∑' k, chapter9Entry2SineTerm (r - 1) a y k))
        - (-(entry2Psin (r - 1) a y))) = 0 := by
      rw [htsum, sub_self]
    have hDy := hD y
    rw [h0] at hDy
    exact hDy.hasDerivWithinAt
  have hconst := constant_of_has_deriv_right_zero hcont hderiv
  have hx0mem : x0 ∈ Set.Icc 0 x0 := ⟨hx0.1, le_rfl⟩
  have hD0 : ((fun z : ℝ => ∑' k, chapter9Entry2CosineTerm r a z k)
        - entry2Pcos r a) x0
      = ((fun z : ℝ => ∑' k, chapter9Entry2CosineTerm r a z k)
        - entry2Pcos r a) 0 :=
    hconst x0 hx0mem
  simp only [Pi.sub_apply] at hD0
  have hS0 : (∑' k, chapter9Entry2CosineTerm r a 0 k)
      = chapter9Entry2Constant r a := by
    unfold chapter9Entry2Constant
    apply tsum_congr
    intro k
    exact cosineTerm_zero_eq r a k
  have hP0 : entry2Pcos r a 0 = chapter9Entry2Constant r a :=
    Pcos_zero r a hr2 he
  have hSeq : (∑' k, chapter9Entry2CosineTerm r a x0 k)
      = entry2Pcos r a x0 := by
    linarith [hD0, hS0, hP0]
  have hsum := (summable_cosineTerm r a x0 hr2).hasSum
  rw [hSeq] at hsum
  exact hsum

theorem step_sine (r : ℕ) (a : ℝ)
    (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ)) (hr : 3 ≤ r)
    (IH : ∀ x ∈ Set.Ico (0 : ℝ) Real.pi,
      HasSum (chapter9Entry2CosineTerm (r - 1) a x) (entry2Pcos (r - 1) a x))
    (x0 : ℝ) (hx0 : x0 ∈ Set.Ico (0 : ℝ) Real.pi) :
    HasSum (chapter9Entry2SineTerm r a x0) (entry2Psin r a x0) := by
  have hr2 : 2 ≤ r := by omega
  have hS : ∀ y : ℝ, HasDerivAt
      (fun z : ℝ => ∑' k, chapter9Entry2SineTerm r a z k)
      (∑' k, chapter9Entry2CosineTerm (r - 1) a y k) y :=
    fun y => hasDerivAt_tsum_sine r a ha hr y
  have hP : ∀ y : ℝ, HasDerivAt (entry2Psin r a)
      (entry2Pcos (r - 1) a y) y :=
    fun y => hasDerivAt_Psin r a y hr2
  have hD : ∀ y : ℝ, HasDerivAt
      ((fun z : ℝ => ∑' k, chapter9Entry2SineTerm r a z k) - entry2Psin r a)
      ((∑' k, chapter9Entry2CosineTerm (r - 1) a y k)
        - entry2Pcos (r - 1) a y) y :=
    fun y => (hS y).sub (hP y)
  have hcont : ContinuousOn
      ((fun z : ℝ => ∑' k, chapter9Entry2SineTerm r a z k) - entry2Psin r a)
      (Set.Icc 0 x0) := by
    have hC : Continuous
        ((fun z : ℝ => ∑' k, chapter9Entry2SineTerm r a z k) - entry2Psin r a) :=
      continuous_iff_continuousAt.mpr (fun y => (hD y).continuousAt)
    exact hC.continuousOn
  have hderiv : ∀ y ∈ Set.Ico 0 x0, HasDerivWithinAt
      ((fun z : ℝ => ∑' k, chapter9Entry2SineTerm r a z k) - entry2Psin r a)
      0 (Set.Ici y) y := by
    intro y hy
    have hyIco : y ∈ Set.Ico (0 : ℝ) Real.pi := ⟨hy.1, lt_of_lt_of_le hy.2 hx0.2.le⟩
    have hIH := IH y hyIco
    have htsum : (∑' k, chapter9Entry2CosineTerm (r - 1) a y k)
        = entry2Pcos (r - 1) a y := hIH.tsum_eq
    have h0 : ((∑' k, chapter9Entry2CosineTerm (r - 1) a y k)
        - entry2Pcos (r - 1) a y) = 0 := by
      rw [htsum, sub_self]
    have hDy := hD y
    rw [h0] at hDy
    exact hDy.hasDerivWithinAt
  have hconst := constant_of_has_deriv_right_zero hcont hderiv
  have hx0mem : x0 ∈ Set.Icc 0 x0 := ⟨hx0.1, le_rfl⟩
  have hD0 : ((fun z : ℝ => ∑' k, chapter9Entry2SineTerm r a z k)
        - entry2Psin r a) x0
      = ((fun z : ℝ => ∑' k, chapter9Entry2SineTerm r a z k)
        - entry2Psin r a) 0 :=
    hconst x0 hx0mem
  simp only [Pi.sub_apply] at hD0
  have hS0 : (∑' k, chapter9Entry2SineTerm r a 0 k) = 0 := by
    have hfun : ∀ k, chapter9Entry2SineTerm r a 0 k = 0 :=
      fun k => sineTerm_zero_eq r a k
    rw [tsum_congr hfun]
    exact tsum_zero
  have hP0 : entry2Psin r a 0 = 0 := Psin_zero r a hr2
  have hSeq : (∑' k, chapter9Entry2SineTerm r a x0 k)
      = entry2Psin r a x0 := by
    linarith [hD0, hS0, hP0]
  have hsum := (summable_sineTerm r a x0 hr2).hasSum
  rw [hSeq] at hsum
  exact hsum

theorem entry2Q_step (a : ℝ)
    (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ)) (n : ℕ) (hn : 2 ≤ n)
    (IH : entry2Q a n) : entry2Q a (n + 1) := by
  have hr : 3 ≤ n + 1 := by omega
  have hn1 : n + 1 - 1 = n := by omega
  intro x hx
  rcases Nat.even_or_odd (n + 1) with he | ho
  · constructor
    · intro _
      have hon : Odd n := by
        obtain ⟨m, hm⟩ := he
        exact ⟨m - 1, by omega⟩
      have IH' : ∀ y ∈ Set.Ico (0 : ℝ) Real.pi,
          HasSum (chapter9Entry2SineTerm (n + 1 - 1) a y)
            (entry2Psin (n + 1 - 1) a y) := by
        intro y hy
        have hcon := IH y hy
        rw [hn1]
        exact hcon.2 hon
      exact step_cosine (n + 1) a ha hr he IH' x hx
    · intro ho'
      obtain ⟨m, hm⟩ := he
      obtain ⟨k, hk⟩ := ho'
      omega
  · constructor
    · intro he'
      obtain ⟨m, hm⟩ := he'
      obtain ⟨k, hk⟩ := ho
      omega
    · intro _
      have hen : Even n := by
        obtain ⟨m, hm⟩ := ho
        exact ⟨m, by omega⟩
      have IH' : ∀ y ∈ Set.Ico (0 : ℝ) Real.pi,
          HasSum (chapter9Entry2CosineTerm (n + 1 - 1) a y)
            (entry2Pcos (n + 1 - 1) a y) := by
        intro y hy
        have hcon := IH y hy
        rw [hn1]
        exact hcon.1 hen
      exact step_sine (n + 1) a ha hr IH' x hx

theorem entry2Q_all_aux (a : ℝ)
    (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ)) :
    ∀ n : ℕ, entry2Q a (2 + n) := by
  intro n
  induction n with
  | zero =>
    change entry2Q a 2
    exact entry2Q_two a ha
  | succ n IH =>
    have h := entry2Q_step a ha (2 + n) (by omega) IH
    have heq : 2 + (n + 1) = (2 + n) + 1 := by omega
    rw [heq]
    exact h

theorem entry2Q_all (a : ℝ)
    (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ)) (r : ℕ) (hr : 2 ≤ r) :
    entry2Q a r := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hr
  rw [hn]
  exact entry2Q_all_aux a ha n

/-- Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 9.

Proves `Wanted` entry `ramanujan_part1_ch9_entry2`.
-/
theorem ramanujan_part1_ch9_entry2 (r : ℕ) (a x : ℝ)
    (hr : 2 ≤ r)
    (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ))
    (hxLower : 0 < x) (hxUpper : x < Real.pi) :
    Summable (chapter9Entry2ConstantTerm r a) ∧
      ((Even r ∧
          (∀ k ∈ range (r / 2),
            Summable (chapter9Entry2ConstantTerm (r - 2 * k) a)) ∧
          Tendsto
            (fun N : ℕ =>
              ∑ k ∈ range N, chapter9Entry2CosineTerm r a x k)
            atTop
            (𝓝 ((∑ k ∈ range (r / 2),
              (-1 : ℝ) ^ k * chapter9Entry2Constant (r - 2 * k) a *
                x ^ (2 * k) / ((2 * k).factorial : ℝ)) +
              (-1 : ℝ) ^ (r / 2) * Real.pi * x ^ (r - 1) /
                (2 * ((r - 1).factorial : ℝ))))) ∨
        (Odd r ∧
          (∀ k ∈ range ((r - 1) / 2),
            Summable (chapter9Entry2ConstantTerm (r - 1 - 2 * k) a)) ∧
          Tendsto
            (fun N : ℕ =>
              ∑ k ∈ range N, chapter9Entry2SineTerm r a x k)
            atTop
            (𝓝 ((∑ k ∈ range ((r - 1) / 2),
              (-1 : ℝ) ^ k * chapter9Entry2Constant (r - 1 - 2 * k) a *
                x ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)) +
              (-1 : ℝ) ^ ((r - 1) / 2) * Real.pi * x ^ (r - 1) /
                (2 * ((r - 1).factorial : ℝ)))))) := by
  have hkey : ∀ s : ℕ, 2 ≤ s → Summable (chapter9Entry2ConstantTerm s a) :=
    fun s hs => summable_chapter9Entry2ConstantTerm s a hs
  have hQ := entry2Q_all a ha r hr
  have hxIco : x ∈ Set.Ico (0 : ℝ) Real.pi := ⟨le_of_lt hxLower, hxUpper⟩
  have hcon := hQ x hxIco
  refine ⟨hkey r hr, ?_⟩
  rcases Nat.even_or_odd r with he | ho
  · left
    refine ⟨he, ?_, ?_⟩
    · intro k hk
      simp only [Finset.mem_range] at hk
      apply hkey
      obtain ⟨m, hm⟩ := he
      omega
    · have hHas := hcon.1 he
      change Tendsto (fun N : ℕ => ∑ k ∈ range N, chapter9Entry2CosineTerm r a x k)
        atTop (𝓝 (entry2Pcos r a x))
      exact hHas.tendsto_sum_nat
  · right
    refine ⟨ho, ?_, ?_⟩
    · intro k hk
      simp only [Finset.mem_range] at hk
      apply hkey
      obtain ⟨m, hm⟩ := ho
      omega
    · have hHas := hcon.2 ho
      change Tendsto (fun N : ℕ => ∑ k ∈ range N, chapter9Entry2SineTerm r a x k)
        atTop (𝓝 (entry2Psin r a x))
      exact hHas.tendsto_sum_nat

end
end Entry2
end Ramanujan.Part1Ch9
end
