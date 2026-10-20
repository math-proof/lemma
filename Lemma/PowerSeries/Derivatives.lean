import Mathlib
import sympy.Basic
import sympy.series.formal.Derivatives
open PowerSeries Polynomial
open scoped PowerSeries
open AlgebraicCombinatorics.FPS


/--
[Derivatives](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Derivatives.lean)
-/
@[path]
private lemma coeff_derivative_eq
  [CommSemiring R]
-- given
  (f : R⟦X⟧)
  (n : ℕ) :
-- imply
  PowerSeries.coeff n (PowerSeries.derivative f) = PowerSeries.coeff (n + 1) f * (n + 1) := by
-- proof
  apply AlgebraicCombinatorics.FPS.coeff_derivative_eq

/--
[Derivatives](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Derivatives.lean)
-/
@[path]
private lemma derivative_eq_mk
  [CommSemiring R]
-- given
  (f : R⟦X⟧) :
-- imply
  PowerSeries.derivative f = PowerSeries.mk (fun n => (n + 1) * PowerSeries.coeff (n + 1) f) := by
-- proof
  apply AlgebraicCombinatorics.FPS.derivative_eq_mk

set_option linter.deprecated false in
/--
[Derivatives](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Derivatives.lean)
-/
@[path]
private lemma derivative_eq_derivativeFun
  [CommSemiring R]
-- given
  (f : R⟦X⟧) :
-- imply
  PowerSeries.derivative f = PowerSeries.derivativeFun f := by
-- proof
  apply AlgebraicCombinatorics.FPS.derivative_eq_derivativeFun

/--
[Derivatives](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Derivatives.lean)
-/
@[path]
private lemma derivative_coeff_formula
  [CommSemiring R]
-- given
  (f : R⟦X⟧)
  (n : ℕ) :
-- imply
  PowerSeries.coeff n (PowerSeries.derivative f) = (n + 1) * PowerSeries.coeff (n + 1) f := by
-- proof
  apply AlgebraicCombinatorics.FPS.derivative_coeff_formula

/--
[Derivatives](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Derivatives.lean)
-/
@[path]
private lemma derivative_X_pow_succ
  [CommSemiring R]
-- given
  (n : ℕ) :
-- imply
  PowerSeries.derivative ((PowerSeries.X : R⟦X⟧) ^ (n + 1)) = (n + 1 : R) • PowerSeries.X ^ n := by
-- proof
  apply AlgebraicCombinatorics.FPS.derivative_X_pow_succ

/--
[Derivatives](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Derivatives.lean)
-/
@[path]
private lemma derivative_X_pow_of_pos
  [CommSemiring R]
-- given
  {n : ℕ}
  (hn : 0 < n) :
-- imply
  PowerSeries.derivative ((PowerSeries.X : R⟦X⟧) ^ n) = (n : R) • PowerSeries.X ^ (n - 1) := by
-- proof
  apply AlgebraicCombinatorics.FPS.derivative_X_pow_of_pos hn

/--
[Derivatives](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Derivatives.lean)
-/
@[path]
private lemma derivative_add
  [CommSemiring R]
-- given
  (f g : R⟦X⟧) :
-- imply
  PowerSeries.derivative (f + g) = PowerSeries.derivative f + PowerSeries.derivative g := by
-- proof
  apply AlgebraicCombinatorics.FPS.derivative_add

/--
[Derivatives](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Derivatives.lean)
-/
@[path]
private lemma derivative_neg
  [CommRing R]
-- given
  (f : R⟦X⟧) :
-- imply
  PowerSeries.derivative (-f) = -PowerSeries.derivative f := by
-- proof
  apply AlgebraicCombinatorics.FPS.derivative_neg

/--
[Derivatives](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Derivatives.lean)
-/
@[path]
private lemma derivative_sub
  [CommRing R]
-- given
  (f g : R⟦X⟧) :
-- imply
  PowerSeries.derivative (f - g) = PowerSeries.derivative f - PowerSeries.derivative g := by
-- proof
  apply AlgebraicCombinatorics.FPS.derivative_sub

/--
[Derivatives](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Derivatives.lean)
-/
@[path]
private lemma derivative_sum
  [CommSemiring R]
-- given
  {ι : Type*}
  (s : Finset ι)
  (f : ι → R⟦X⟧) :
-- imply
  PowerSeries.derivative (∑ i ∈ s, f i) = ∑ i ∈ s, PowerSeries.derivative (f i) := by
-- proof
  apply AlgebraicCombinatorics.FPS.derivative_sum

/--
[Derivatives](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Derivatives.lean)
-/
@[path]
private lemma summableFPS_derivative
  [CommRing R]
-- given
  {ι : Type*}
  (f : ι → R⟦X⟧)
  (hf : SummableFPS f) :
-- imply
  SummableFPS (fun i => PowerSeries.derivative (f i)) := by
-- proof
  apply AlgebraicCombinatorics.FPS.summableFPS_derivative f hf

/--
[Derivatives](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Derivatives.lean)
-/
@[path]
private lemma derivative_summableFPSSum
  [CommRing R]
-- given
  {ι : Type*}
  (f : ι → R⟦X⟧)
  (hf : SummableFPS f) :
-- imply
  PowerSeries.derivative (summableFPSSum f hf) =
    summableFPSSum (fun i => PowerSeries.derivative (f i)) (AlgebraicCombinatorics.FPS.summableFPS_derivative f hf) := by
-- proof
  apply AlgebraicCombinatorics.FPS.derivative_summableFPSSum

/--
[Derivatives](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Derivatives.lean)
-/
@[path]
private lemma derivative_smul
  [CommSemiring R]
-- given
  (c : R)
  (f : R⟦X⟧) :
-- imply
  PowerSeries.derivative (c • f) = c • PowerSeries.derivative f := by
-- proof
  apply AlgebraicCombinatorics.FPS.derivative_smul

/--
[Derivatives](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Derivatives.lean)
-/
@[path]
private lemma derivative_C_mul
  [CommSemiring R]
-- given
  (c : R)
  (f : R⟦X⟧) :
-- imply
  PowerSeries.derivative (PowerSeries.C c * f) = PowerSeries.C c * PowerSeries.derivative f := by
-- proof
  apply AlgebraicCombinatorics.FPS.derivative_C_mul

/--
[Derivatives](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Derivatives.lean)
-/
@[path]
private lemma derivative_mul
  [CommSemiring R]
-- given
  (f g : R⟦X⟧) :
-- imply
  PowerSeries.derivative (f * g) = PowerSeries.derivative f * g + f * PowerSeries.derivative g := by
-- proof
  apply AlgebraicCombinatorics.FPS.derivative_mul

/--
[Derivatives](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Derivatives.lean)
-/
@[path]
private lemma derivative_div
  [Field K]
-- given
  (f g : K⟦X⟧)
  (hg : constantCoeff g ≠ 0) :
-- imply
  PowerSeries.derivative (f * g⁻¹) = (PowerSeries.derivative f * g - f * PowerSeries.derivative g) * g⁻¹ ^ 2 := by
-- proof
  apply AlgebraicCombinatorics.FPS.derivative_div f g hg

/--
[Derivatives](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Derivatives.lean)
-/
@[path]
private lemma derivative_pow'
  [CommRing A]
-- given
  (g : A⟦X⟧)
  (n : ℕ) :
-- imply
  PowerSeries.derivative (g ^ n) = n * g ^ (n - 1) * PowerSeries.derivative g := by
-- proof
  apply AlgebraicCombinatorics.FPS.derivative_pow'

/--
[Derivatives](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Derivatives.lean)
-/
@[path]
private lemma derivative_comp
  [CommRing A]
-- given
  (f g : A⟦X⟧)
  (hg : PowerSeries.HasSubst g) :
-- imply
  PowerSeries.derivative (f.subst g) = (PowerSeries.derivative f).subst g * PowerSeries.derivative g := by
-- proof
  apply AlgebraicCombinatorics.FPS.derivative_comp f g hg

/--
[Derivatives](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Derivatives.lean)
-/
@[path]
private lemma derivative_eq_imp_diff_const
  [CommRing R] [IsAddTorsionFree R]
-- given
  {f g : R⟦X⟧}
  (h : PowerSeries.derivative f = PowerSeries.derivative g) :
-- imply
  ∀ n : ℕ, n ≠ 0 → PowerSeries.coeff n (f - g) = 0 := by
-- proof
  apply AlgebraicCombinatorics.FPS.derivative_eq_imp_diff_const h

/--
[Derivatives](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Derivatives.lean)
-/
@[path]
private lemma eq_of_derivative_eq_of_constantCoeff_eq
  [CommRing R] [IsAddTorsionFree R]
-- given
  {f g : R⟦X⟧}
  (hD : PowerSeries.derivative f = PowerSeries.derivative g)
  (hc : constantCoeff f = constantCoeff g) :
-- imply
  f = g := by
-- proof
  apply AlgebraicCombinatorics.FPS.eq_of_derivative_eq_of_constantCoeff_eq hD hc

/--
[Derivatives](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Derivatives.lean)
-/
@[path]
private lemma derivative_zero
  [CommSemiring R] :
-- imply
  PowerSeries.derivative (0 : R⟦X⟧) = 0 := by
-- proof
  apply AlgebraicCombinatorics.FPS.derivative_zero

/--
[Derivatives](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Derivatives.lean)
-/
@[path]
private lemma derivative_C
  [CommSemiring R]
-- given
  (c : R) :
-- imply
  PowerSeries.derivative (PowerSeries.C c) = 0 := by
-- proof
  apply AlgebraicCombinatorics.FPS.derivative_C

/--
[Derivatives](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Derivatives.lean)
-/
@[path]
private lemma derivative_X
  [CommSemiring R] :
-- imply
  PowerSeries.derivative (X : R⟦X⟧) = 1 := by
-- proof
  apply AlgebraicCombinatorics.FPS.derivative_X

/--
[Derivatives](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Derivatives.lean)
-/
@[path]
private lemma derivative_one
  [CommSemiring R] :
-- imply
  PowerSeries.derivative (1 : R⟦X⟧) = 0 := by
-- proof
  apply AlgebraicCombinatorics.FPS.derivative_one

/--
[Derivatives](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Derivatives.lean)
-/
@[path]
private lemma derivative_coe_polynomial
  [CommSemiring R]
-- given
  (p : R[X]) :
-- imply
  PowerSeries.derivative (p : R⟦X⟧) = (Polynomial.derivative p : R⟦X⟧) := by
-- proof
  apply AlgebraicCombinatorics.FPS.derivative_coe_polynomial


-- created on 2026-10-20
