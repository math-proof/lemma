/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.RingTheory.PowerSeries.InfiniteProducts
import Lemma.PowerSeries.InfiniteProducts
import Theorem.RingTheory.PowerSeries.ExpLog.Part4
/-!
# Exponentials and Logarithms of Formal Power Series

This file formalizes Section 7.8 (Exponentials and logarithms) from the Algebraic Combinatorics
textbook. It develops the theory of exponential and logarithm operations on formal power series
over ℚ-algebras.

## Convention

Throughout this file, `K` is assumed to be a commutative ℚ-algebra (Convention 7.8.1 in the text).
This allows division by positive integers.

## Main Definitions

* `PowerSeries.logbar`: The FPS `∑_{n≥1} (-1)^{n-1}/n · x^n`, the Mercator series for `log(1+x)`.
* `PowerSeries.expbar`: The FPS `exp - 1 = ∑_{n≥1} 1/n! · x^n`.
* `PowerSeries.PowerSeries₀`: The set of FPS with constant term 0.
* `PowerSeries.PowerSeries₁`: The set of FPS with constant term 1.
* `PowerSeries.Exp`: The map `g ↦ exp ∘ g` from `K⟦X⟧₀` to `K⟦X⟧₁`.
* `PowerSeries.Log`: The map `f ↦ logbar ∘ (f - 1)` from `K⟦X⟧₁` to `K⟦X⟧₀`.
* `PowerSeries.loder`: The logarithmic derivative `f'/f` for FPS with constant term 1.

## Main Results

* `PowerSeries.derivative_exp`: `exp' = exp` (Definition 7.8.2 / Proposition 7.8.3)
* `PowerSeries.derivative_expbar`: `expbar' = exp` (Proposition 7.8.3)
* `PowerSeries.derivative_logbar`: `logbar' = (1+x)⁻¹` (Proposition 7.8.3)
* `PowerSeries.derivative_exp_comp`: `(exp ∘ g)' = (exp ∘ g) · g'` (Proposition 7.8.3(a))
* `PowerSeries.derivative_expbar_comp`: `(expbar ∘ g)' = (exp ∘ g) · g'` (Proposition 7.8.3(a))
* `PowerSeries.derivative_logbar_comp`: `(logbar ∘ g)' = (1+g)⁻¹ · g'` (Proposition 7.8.3(b))
* `PowerSeries.expbar_comp_logbar`: `expbar ∘ logbar = x` (Theorem 7.8.5)
* `PowerSeries.logbar_comp_expbar`: `logbar ∘ expbar = x` (Theorem 7.8.5)
* `PowerSeries.Log_Exp` and `PowerSeries.Exp_Log`: `Exp` and `Log` are mutually inverse (Lemma 7.8.8)
* `PowerSeries.Exp_add`: `Exp(f + g) = Exp(f) · Exp(g)` (Lemma 7.8.9)
* `PowerSeries.Log_mul`: `Log(fg) = Log(f) + Log(g)` (Lemma 7.8.9)
* `PowerSeries.Exp_Log_groupIso`: `Exp` is a group isomorphism (Theorem 7.8.11)
* `PowerSeries.loder_mul`: `loder(fg) = loder(f) + loder(g)` (Proposition 7.8.14)
* `PowerSeries.loder_inv`: `loder(f⁻¹) = -loder(f)` (Corollary 7.8.16)
* `PowerSeries.Log_tprod`: `Log(∏ fᵢ) = ∑ Log(fᵢ)` for infinite products (Proposition prop.fps.Exp-Log-infprod)
* `PowerSeries.Exp_sum`: `Exp(∑ gᵢ) = ∏ Exp(gᵢ)` for infinite sums (Proposition prop.fps.Exp-Log-infsum)

## References

* [Darij Grinberg, *Algebraic Combinatorics*, Section 7.8]
* [Grinberg-Reiner, *logexp*, Lemma 0.4 and Theorem 0.1]

## Tags

power series, exponential, logarithm, formal power series
-/


namespace PowerSeries

open Nat Finset

variable (K : Type*) [CommRing K] [Algebra ℚ K]

variable {K}

section ExpLogMaps

variable (K : Type*) [CommRing K] [Algebra ℚ K]

variable {K}

/-- The exponential map `Exp : K⟦X⟧₀ → K⟦X⟧₁` defined by `g ↦ exp ∘ g`.
This is Definition 7.8.6(c) (def.fps.Exp-Log-maps). -/
noncomputable def Exp (g : PowerSeries₀ (R := K)) : PowerSeries₁ (R := K) :=
  ⟨(exp K).subst g.val, exp_subst_mem_PowerSeries₁ g.property⟩

/-- The logarithm map `Log : K⟦X⟧₁ → K⟦X⟧₀` defined by `f ↦ logbar ∘ (f - 1)`.
This is Definition 7.8.6(c) (def.fps.Exp-Log-maps). -/
noncomputable def Log (f : PowerSeries₁ (R := K)) : PowerSeries₀ (R := K) :=
  ⟨(logbar K).subst (f.val - 1), logbar_subst_sub_one_mem_PowerSeries₀ f.property⟩

/-! ## Section 7.8.4: Addition to multiplication -/

end ExpLogMaps

/-! ## Section 7.8.5: The logarithmic derivative -/


section LogarithmicDerivative

variable {R : Type*} [Field R]

/-- **Definition 7.8.12 (def.fps.loder.1)**: The logarithmic derivative.

For any FPS `f ∈ R⟦X⟧₁` (i.e., with constant term 1), we define the *logarithmic derivative*
`loder f ∈ R⟦X⟧` to be the FPS `f'/f`.

This is well-defined since `f` is invertible when `constantCoeff f = 1`
(see `isUnit_of_constantCoeff_eq_one`).

**Important**: This definition does NOT require `R` to be a ℚ-algebra. The definition makes
sense over any field. The name "logarithmic derivative" comes from Proposition 7.8.13
(`loder_eq_derivative_Log`), which shows that over ℚ-algebras, `loder f = (Log f)'`.

## Properties

* `loder_one`: `loder 1 = 0`
* `loder_mul`: `loder(fg) = loder f + loder g` (Proposition 7.8.14)
* `loder_inv`: `loder(f⁻¹) = -loder f` (Corollary 7.8.16)
* `loder_prod`: `loder(∏ fᵢ) = ∑ loder fᵢ` (Corollary 7.8.15)
-/
noncomputable def loder (f : R⟦X⟧) : R⟦X⟧ := d⁄dX f * f⁻¹

/-! ### Well-definedness of loder (def.fps.loder.1)

The logarithmic derivative is well-defined for FPS with constant term 1 because such FPS
are invertible. The following lemmas establish this. -/

end LogarithmicDerivative

/-! ## Section 7.10.2: Exp and Log for Infinite Products

The Exp and Log maps convert between infinite sums and products.
These results require K to be a ℚ-algebra for the formal exp and log to be defined.

Propositions prop.fps.Exp-Log-infsum and prop.fps.Exp-Log-infprod state:
- `Exp(∑_{i ∈ I} f_i) = ∏_{i ∈ I} Exp(f_i)` for summable families in `K⟦X⟧_0`
- `Log(∏_{i ∈ I} f_i) = ∑_{i ∈ I} Log(f_i)` for multipliable families in `K⟦X⟧_1`
-/


section ExpLogInfinite

variable {K : Type*} [CommRing K] [Algebra ℚ K]

variable {I : Type*}

/-! ### Summable families in K⟦X⟧₀ -/


/-- A family of FPS in `K⟦X⟧₀` is summable if for each coefficient index n,
only finitely many family members have nonzero n-th coefficient.

This is the notion of summability appropriate for `K⟦X⟧₀`. -/
def SummableFPS₀ (f : I → PowerSeries₀ (R := K)) : Prop :=
  ∀ n : ℕ, {i : I | (f i).val.coeff n ≠ 0}.Finite

/-- The coefficient-wise sum of a summable family in `K⟦X⟧₀`.

**Important:** This is defined coefficient-wise using `mk`, NOT using `finsum` on the entire
power series. The reason is that `finsum` returns 0 when the support is infinite, but
`SummableFPS₀` only guarantees finite support for each coefficient, not for the entire family.

For each coefficient n, only finitely many terms contribute (by `SummableFPS₀`), so the
finsum `∑ᶠ i, coeff n (f i).val` is well-defined and equals a finite sum. -/
noncomputable def summableFPS₀Sum (f : I → PowerSeries₀ (R := K)) (_hf : SummableFPS₀ f) :
    PowerSeries₀ (R := K) :=
  ⟨mk fun n => ∑ᶠ i, coeff n (f i).val, by
    rw [mem_PowerSeries₀_iff, ← coeff_zero_eq_constantCoeff_apply, coeff_mk]
    apply finsum_eq_zero_of_forall_eq_zero
    intro i
    rw [coeff_zero_eq_constantCoeff_apply]
    exact (f i).property⟩

/-! ### Multipliable families in K⟦X⟧₁ -/


/-- A family of FPS in `K⟦X⟧₁` is multipliable if for each coefficient index n,
the n-th coefficient of the product is finitely determined.

This is the notion of multipliability appropriate for `K⟦X⟧₁`. -/
def MultipliableFPS₁ (f : I → PowerSeries₁ (R := K)) : Prop :=
  PowerSeries.Multipliable (fun i => (f i).val)

end ExpLogInfinite
end PowerSeries
