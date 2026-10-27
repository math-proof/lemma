import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.RingTheory.PowerSeries.Derivatives
import Lemma.PowerSeries.FPSDefinition
open PowerSeries Polynomial
open scoped PowerSeries
open AlgebraicCombinatorics.FPS


section
-- ac-theorems


open PowerSeries Polynomial
open scoped PowerSeries
open AlgebraicCombinatorics.FPS (SummableFPS summableFPSSum coeff_summableFPSSum)

namespace AlgebraicCombinatorics.FPS


section Definition

variable {R : Type*} [CommSemiring R]


/-- **Definition def.fps.deriv**: The n-th coefficient of the derivative of f
equals (n+1) times the (n+1)-th coefficient of f.

This is `PowerSeries.coeff_derivative` in Mathlib. -/
lemma coeff_derivative_eq (f : R⟦X⟧) (n : ℕ) :
    PowerSeries.coeff n (d⁄dX f) = PowerSeries.coeff (n + 1) f * (n + 1) :=
  PowerSeries.coeff_derivative f n

/-- **Definition def.fps.deriv**: The derivative expressed in terms of `mk`.

For `f = ∑ fₙ xⁿ`, the textbook defines `f' := ∑_{n>0} n · fₙ · x^{n-1}`.
Reindexing gives `f' = mk (fun m => (m+1) * f_{m+1})`. -/
lemma derivative_eq_mk (f : R⟦X⟧) :
    d⁄dX f = PowerSeries.mk (fun n => (n + 1) * PowerSeries.coeff (n + 1) f) := by
  ext n
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mk, mul_comm]

set_option linter.deprecated false in
/-- The derivative operation is exactly `derivativeFun` from Mathlib. -/
lemma derivative_eq_derivativeFun (f : R⟦X⟧) :
    d⁄dX f = PowerSeries.derivativeFun f := rfl

/-- Alternative characterization: the coefficient of xⁿ in f' is (n+1) · f_{n+1}.
This is the "shift and multiply" form of the derivative. -/
lemma derivative_coeff_formula (f : R⟦X⟧) (n : ℕ) :
    PowerSeries.coeff n (d⁄dX f) = (n + 1) * PowerSeries.coeff (n + 1) f := by
  rw [PowerSeries.coeff_derivative, mul_comm]

/-- The derivative of X^(n+1) is (n+1) * X^n. This is a convenient form for induction. -/
@[simp]
lemma derivative_X_pow_succ (n : ℕ) :
    d⁄dX ((PowerSeries.X : R⟦X⟧) ^ (n + 1)) = (n + 1 : R) • PowerSeries.X ^ n := by
  ext m
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_X_pow, PowerSeries.coeff_smul,
      PowerSeries.coeff_X_pow]
  by_cases h : m + 1 = n + 1
  · simp only [h, ↓reduceIte]
    have : m = n := by omega
    simp [this]
  · simp only [h, ↓reduceIte]
    have : m ≠ n := by omega
    simp [this]

/-- Derivative of X^n for n > 0. -/
lemma derivative_X_pow_of_pos {n : ℕ} (hn : 0 < n) :
    d⁄dX ((PowerSeries.X : R⟦X⟧) ^ n) = (n : R) • PowerSeries.X ^ (n - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)
  simp only [derivative_X_pow_succ, Nat.succ_sub_one, Nat.cast_succ]

end Definition


section DerivativeRules

variable {R : Type*} [CommSemiring R]


/-- **Theorem thm.fps.deriv.rules (a)**: Derivative is additive. -/
lemma derivative_add (f g : R⟦X⟧) : d⁄dX (f + g) = d⁄dX f + d⁄dX g :=
  map_add (d⁄dX) f g

/-- Derivative of negation: `(-f)' = -f'`. -/
@[simp]
lemma derivative_neg {R : Type*} [CommRing R] (f : R⟦X⟧) : d⁄dX (-f) = -d⁄dX f :=
  map_neg (d⁄dX) f

/-- Derivative of subtraction: `(f - g)' = f' - g'`. -/
@[simp]
lemma derivative_sub {R : Type*} [CommRing R] (f g : R⟦X⟧) :
    d⁄dX (f - g) = d⁄dX f - d⁄dX g :=
  map_sub (d⁄dX) f g


/-- **Theorem thm.fps.deriv.rules (b)** (finite version):
Derivative commutes with finite sums. -/
lemma derivative_sum {ι : Type*} (s : Finset ι) (f : ι → R⟦X⟧) :
    d⁄dX (∑ i ∈ s, f i) = ∑ i ∈ s, d⁄dX (f i) :=
  map_sum (d⁄dX) f s

-- Note: SummableFPS and summableFPSSum are imported from FPSDefinition.lean
-- The following uses the canonical definitions from that file.
-- These require [CommRing R] rather than [CommSemiring R]

variable {R' : Type*} [CommRing R']

/-- If (fᵢ) is a summable family, then (fᵢ') is also summable. -/
lemma summableFPS_derivative {ι : Type*} (f : ι → R'⟦X⟧) (hf : SummableFPS f) :
    SummableFPS (fun i => d⁄dX (f i)) := by
  intro n
  have h := hf (n + 1)
  apply Set.Finite.subset h
  intro i hi
  simp only [Set.mem_ofPred_eq] at hi ⊢
  rw [PowerSeries.coeff_derivative] at hi
  intro hcontra
  apply hi
  rw [hcontra, zero_mul]

/-- **Theorem thm.fps.deriv.rules (b)** (infinite version):
Derivative commutes with infinite summable sums.

If (fᵢ)_{i ∈ I} is a summable family of FPSs, then (fᵢ')_{i ∈ I} is summable
and (∑ fᵢ)' = ∑ fᵢ'. -/
lemma derivative_summableFPSSum {ι : Type*} (f : ι → R'⟦X⟧) (hf : SummableFPS f) :
    d⁄dX (summableFPSSum f hf) =
      summableFPSSum (fun i => d⁄dX (f i)) (summableFPS_derivative f hf) := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_derivative, coeff_summableFPSSum, coeff_summableFPSSum]
  -- Need: (∑ᶠ i, coeff (n + 1) (f i)) * (n + 1) = ∑ᶠ i, coeff n (d⁄dX (f i))
  -- coeff n (d⁄dX (f i)) = coeff (n + 1) (f i) * (n + 1)
  have heq : ∀ i, coeff n (d⁄dX (f i)) = coeff (n + 1) (f i) * (n + 1) := fun i =>
    PowerSeries.coeff_derivative (f i) n
  simp_rw [heq]
  -- Now need: (∑ᶠ i, coeff (n + 1) (f i)) * (n + 1) = ∑ᶠ i, coeff (n + 1) (f i) * (n + 1)
  have hsupport : (Function.support (fun i => coeff (n + 1) (f i))).Finite := hf (n + 1)
  rw [finsum_mul' _ _ hsupport]


/-- **Theorem thm.fps.deriv.rules (c)**: Derivative commutes with scalar multiplication. -/
lemma derivative_smul (c : R) (f : R⟦X⟧) : d⁄dX (c • f) = c • d⁄dX f :=
  (d⁄dX).map_smul c f

/-- Variant with `C c * f` instead of `c • f`. -/
lemma derivative_C_mul (c : R) (f : R⟦X⟧) :
    d⁄dX (PowerSeries.C c * f) = PowerSeries.C c * d⁄dX f := by
  rw [← PowerSeries.smul_eq_C_mul, ← PowerSeries.smul_eq_C_mul, derivative_smul]


/-- **Theorem thm.fps.deriv.rules (d)**: Leibniz rule for power series. -/
lemma derivative_mul (f g : R⟦X⟧) :
    d⁄dX (f * g) = d⁄dX f * g + f * d⁄dX g := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  ring


variable {K : Type*} [Field K]

/-- **Theorem thm.fps.deriv.rules (e)**: Quotient rule for power series.

Note: In Mathlib, this is stated as `(f⁻¹)' = -f⁻¹² · f'`.
The full quotient rule follows from combining this with Leibniz. -/
lemma derivative_div (f g : K⟦X⟧) (hg : constantCoeff g ≠ 0) :
    d⁄dX (f * g⁻¹) = (d⁄dX f * g - f * d⁄dX g) * g⁻¹ ^ 2 := by
  have hg_unit : g * g⁻¹ = 1 := g.mul_inv_cancel hg
  have hg_unit' : g⁻¹ * g = 1 := g.inv_mul_cancel hg
  rw [derivative_mul, derivative_inv']
  have h1 : d⁄dX f * g⁻¹ + f * (-(g⁻¹ ^ 2) * d⁄dX g)
          = d⁄dX f * g⁻¹ - f * g⁻¹ ^ 2 * d⁄dX g := by ring
  rw [h1]
  have h2 : d⁄dX f * g⁻¹ = d⁄dX f * g⁻¹ ^ 2 * g := by
    rw [sq, mul_assoc, mul_assoc, ← mul_assoc g⁻¹ g⁻¹ g]
    rw [mul_assoc g⁻¹, hg_unit', mul_one]
  rw [h2]
  ring


variable {A : Type*} [CommRing A]

/-- **Theorem thm.fps.deriv.rules (f)**: Power rule for power series. -/
lemma derivative_pow' (g : A⟦X⟧) (n : ℕ) :
    d⁄dX (g ^ n) = n * g ^ (n - 1) * d⁄dX g :=
  PowerSeries.derivative_pow g n


/-- **Theorem thm.fps.deriv.rules (g)**: Chain rule for power series.

This holds when `g` has nilpotent constant coefficient (in particular when `[x⁰]g = 0`). -/
lemma derivative_comp (f g : A⟦X⟧) (hg : HasSubst g) :
    d⁄dX (f.subst g) = (d⁄dX f).subst g * d⁄dX g :=
  PowerSeries.derivative_subst hg


/-- **Theorem thm.fps.deriv.rules (h)**: Two power series with equal derivatives
differ by a constant.

Note: Mathlib states this as: if `f' = g'` and `f₀ = g₀`, then `f = g`.
We state the equivalent: if `f' = g'`, then `f - g` has zero derivative,
hence is constant (all higher coefficients are zero). -/
lemma derivative_eq_imp_diff_const {R : Type*} [CommRing R] [IsAddTorsionFree R]
    {f g : R⟦X⟧} (h : d⁄dX f = d⁄dX g) :
    ∀ n : ℕ, n ≠ 0 → PowerSeries.coeff n (f - g) = 0 := by
  intro n hn
  have heq : PowerSeries.coeff (n - 1) (d⁄dX f) = PowerSeries.coeff (n - 1) (d⁄dX g) := by
    rw [h]
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_derivative] at heq
  rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)] at heq
  rw [map_sub]
  rw [mul_comm, mul_comm (PowerSeries.coeff n g)] at heq
  cases n with
  | zero => exact absurd rfl hn
  | succ m =>
    simp only [Nat.add_sub_cancel] at heq
    rw [← Nat.cast_succ, mul_comm, ← nsmul_eq_mul, mul_comm, ← nsmul_eq_mul,
        smul_right_inj (Nat.succ_ne_zero m)] at heq
    exact sub_eq_zero.mpr heq

/-- Equivalent formulation: if two power series have equal derivatives and equal
constant terms, they are equal. This is `PowerSeries.derivative.ext` in Mathlib. -/
lemma eq_of_derivative_eq_of_constantCoeff_eq {R : Type*} [CommRing R] [IsAddTorsionFree R]
    {f g : R⟦X⟧} (hD : d⁄dX f = d⁄dX g) (hc : constantCoeff f = constantCoeff g) :
    f = g :=
  PowerSeries.derivative.ext hD hc

end DerivativeRules


section Additional

variable {R : Type*} [CommSemiring R]

/-- Derivative of zero is zero. -/
@[simp]
lemma derivative_zero : d⁄dX (0 : R⟦X⟧) = 0 :=
  map_zero (d⁄dX)

/-- Derivative of a constant is zero. -/
@[simp]
lemma derivative_C (c : R) : d⁄dX (PowerSeries.C c) = 0 :=
  PowerSeries.derivative_C

/-- Derivative of X is 1. -/
@[simp]
lemma derivative_X : d⁄dX (X : R⟦X⟧) = 1 :=
  PowerSeries.derivative_X

/-- Derivative of 1 is 0. -/
@[simp]
lemma derivative_one : d⁄dX (1 : R⟦X⟧) = 0 :=
  Derivation.map_one_eq_zero (d⁄dX)

/-- The derivative of a polynomial viewed as a power series equals
the polynomial derivative viewed as a power series. -/
lemma derivative_coe_polynomial (p : R[X]) :
    d⁄dX (p : R⟦X⟧) = (Polynomial.derivative p : R⟦X⟧) :=
  PowerSeries.derivative_coe p

end Additional

end AlgebraicCombinatorics.FPS
end


/--
[Derivatives](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Derivatives.lean)
-/
@[path]
private lemma pv_coeff_derivative_eq
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
private lemma pv_derivative_eq_mk
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
private lemma pv_derivative_eq_derivativeFun
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
private lemma pv_derivative_coeff_formula
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
private lemma pv_derivative_X_pow_succ
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
private lemma pv_derivative_X_pow_of_pos
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
private lemma pv_derivative_add
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
private lemma pv_derivative_neg
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
private lemma pv_derivative_sub
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
private lemma pv_derivative_sum
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
private lemma pv_summableFPS_derivative
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
private lemma pv_derivative_summableFPSSum
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
private lemma pv_derivative_smul
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
private lemma pv_derivative_C_mul
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
private lemma pv_derivative_mul
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
private lemma pv_derivative_div
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
private lemma pv_derivative_pow'
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
private lemma pv_derivative_comp
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
private lemma pv_derivative_eq_imp_diff_const
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
private lemma pv_eq_of_derivative_eq_of_constantCoeff_eq
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
private lemma pv_derivative_zero
  [CommSemiring R] :
-- imply
  PowerSeries.derivative (0 : R⟦X⟧) = 0 := by
-- proof
  apply AlgebraicCombinatorics.FPS.derivative_zero

/--
[Derivatives](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Derivatives.lean)
-/
@[path]
private lemma pv_derivative_C
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
private lemma pv_derivative_X
  [CommSemiring R] :
-- imply
  PowerSeries.derivative (X : R⟦X⟧) = 1 := by
-- proof
  apply AlgebraicCombinatorics.FPS.derivative_X

/--
[Derivatives](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Derivatives.lean)
-/
@[path]
private lemma pv_derivative_one
  [CommSemiring R] :
-- imply
  PowerSeries.derivative (1 : R⟦X⟧) = 0 := by
-- proof
  apply AlgebraicCombinatorics.FPS.derivative_one

/--
[Derivatives](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Derivatives.lean)
-/
@[path]
private lemma pv_derivative_coe_polynomial
  [CommSemiring R]
-- given
  (p : R[X]) :
-- imply
  PowerSeries.derivative (p : R⟦X⟧) = (Polynomial.derivative p : R⟦X⟧) := by
-- proof
  apply AlgebraicCombinatorics.FPS.derivative_coe_polynomial


-- created on 2026-10-20
