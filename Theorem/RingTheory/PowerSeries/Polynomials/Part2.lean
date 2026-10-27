/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2024 AlgebraicCombinatorics Contributors. All rights reserved.
Authors: AlgebraicCombinatorics Contributors
-/
import Mathlib
import Def.RingTheory.PowerSeries.Polynomials.Part2
/-!
# Polynomials

This file formalizes the relationship between polynomials and formal power series (FPS),
following the treatment in the Algebraic Combinatorics book.

## Main Content

The key insight is that polynomials can be viewed as FPSs with only finitely many nonzero
coefficients. In Mathlib:
- `PowerSeries R` (notation: `R⟦X⟧`) is the type of formal power series
- `Polynomial R` (notation: `R[X]`) is the type of univariate polynomials
- `Polynomial.toPowerSeries` embeds polynomials into power series

## Main Definitions

* `FPS.IsPolynomial` - A predicate characterizing when a power series is a polynomial
  (i.e., has only finitely many nonzero coefficients)
* `FPS.polynomialSubalgebra` - The K-subalgebra of polynomial power series (Theorem 7.5.2)
* `FPS.polynomialSubring` - The subring of polynomial power series (Theorem 7.5.2)
* `FPS.polynomialSubmodule` - The K-submodule of polynomial power series (Theorem 7.5.2)
* `FPS.polyEval` - Polynomial evaluation at an element of a K-algebra (Definition 7.5.6)
* Notation `f⦃a⦄` for polynomial evaluation (corresponds to book notation `f[a]`)

## Main Results

* `FPS.isPolynomial_iff_finite_support` - A power series is a polynomial iff it has finite support
* `FPS.isPolynomial_add` - The sum of polynomials is a polynomial
* `FPS.isPolynomial_mul` - The product of polynomials is a polynomial
* `FPS.isPolynomial_neg` - The negation of a polynomial is a polynomial
* `FPS.isPolynomial_sub` - The difference of polynomials is a polynomial

## Evaluation/Substitution (def.pol.subs)

The evaluation of a polynomial `f` at an element `a` of a `K`-algebra `A` is denoted
`polyEval f a` or `f⦃a⦄`. This corresponds to Definition 7.5.6 (def.pol.subs) in the source:
  f[a] := Σ_{n ∈ ℕ} f_n · a^n

Key properties (Theorem 7.5.7, thm.pol.eval.a+b):
- `(f + g)⦃a⦄ = f⦃a⦄ + g⦃a⦄` : `eval_add'`
- `(f * g)⦃a⦄ = f⦃a⦄ * g⦃a⦄` : `eval_mul'`
- `(c • f)⦃a⦄ = c • f⦃a⦄` : `eval_smul'`
- `C(c)⦃a⦄ = algebraMap K A c` : `eval_C'`
- `X⦃a⦄ = a` : `eval_X'`
- `X^i⦃a⦄ = a^i` : `eval_X_pow'`
- `f⦃g⦃a⦄⦄ = (f.comp g)⦃a⦄` : `eval_comp'`

Special cases:
- `f⦃x⦄ = f` : `eval_X_eq_self`
- `f⦃0⦄ = f₀` : `eval_zero_eq_coeff_zero`
- `f⦃1⦄ = sum of coefficients` : `eval_one_eq_sum_coeffs`

## References

* Definition 7.5.1 (def.fps.pol) - Definition of polynomial as FPS with finite support ✓
* Theorem 7.5.2 (thm.fps.pol.ring) - K[x] is a subring of K[[x]] ✓
* Definition 7.5.3 (def.alg.ring) - Definition of (noncommutative) ring
* Definition 7.5.5 (def.alg.Kalg) - Definition of K-algebra
* Definition 7.5.6 (def.pol.subs) - Evaluation/substitution into polynomials ✓
* Theorem 7.5.7 (thm.pol.eval.a+b) - Properties of polynomial evaluation ✓

-/


namespace FPS

open Polynomial PowerSeries

variable {K : Type*} [CommRing K]

/-! ## Polynomials Form a Subring of Power Series

Theorem 7.5.2 (thm.fps.pol.ring): The set K[x] is a subring of K[[x]].
-/


/-- The zero power series is a polynomial. -/
@[simp]
theorem isPolynomial_zero : IsPolynomial (0 : PowerSeries K) := by
  simp only [IsPolynomial]
  have : {n : ℕ | PowerSeries.coeff n (0 : PowerSeries K) ≠ 0} = ∅ := by
    ext n
    simp only [Set.mem_ofPred_eq, map_zero, ne_eq, not_true_eq_false, Set.mem_empty_iff_false]
  rw [this]
  exact Set.finite_empty

/-- The constant power series 1 is a polynomial. -/
@[simp]
theorem isPolynomial_one : IsPolynomial (1 : PowerSeries K) := by
  have h : (1 : PowerSeries K) = ((1 : K[X]) : PowerSeries K) := by
    ext n
    simp only [Polynomial.coeff_coe, Polynomial.coeff_one]
    simp only [PowerSeries.coeff_one]
  rw [h]
  exact isPolynomial_of_polynomial (1 : K[X])

/-- The sum of two polynomial power series is a polynomial.
This is part of Theorem 7.5.2 (thm.fps.pol.ring). -/
theorem isPolynomial_add {f g : PowerSeries K} (hf : IsPolynomial f) (hg : IsPolynomial g) :
    IsPolynomial (f + g) := by
  simp only [IsPolynomial] at *
  have h : {n : ℕ | PowerSeries.coeff n (f + g) ≠ 0} ⊆
      {n : ℕ | PowerSeries.coeff n f ≠ 0} ∪ {n : ℕ | PowerSeries.coeff n g ≠ 0} := by
    intro n hn
    simp only [Set.mem_ofPred_eq, map_add, ne_eq] at hn
    simp only [Set.mem_union, Set.mem_ofPred_eq, ne_eq]
    by_contra hc
    push Not at hc
    rw [hc.1, hc.2, add_zero] at hn
    exact hn rfl
  exact Set.Finite.subset (Set.Finite.union hf hg) h

/-- The product of two polynomial power series is a polynomial.
This is the main content of Theorem 7.5.2 (thm.fps.pol.ring). -/
theorem isPolynomial_mul {f g : PowerSeries K} (hf : IsPolynomial f) (hg : IsPolynomial g) :
    IsPolynomial (f * g) := by
  simp only [IsPolynomial] at *
  -- The support of f*g is contained in {i + j | i ∈ supp f, j ∈ supp g}
  let I := {n : ℕ | PowerSeries.coeff n f ≠ 0}
  let J := {n : ℕ | PowerSeries.coeff n g ≠ 0}
  let S := {n : ℕ | ∃ i ∈ I, ∃ j ∈ J, n = i + j}
  have hS : S.Finite := by
    have hsub : S ⊆ Finset.image₂ (· + ·) hf.toFinset hg.toFinset := by
      intro n ⟨i, hi, j, hj, hn⟩
      simp only [Finset.coe_image₂, Set.mem_image2]
      refine ⟨i, ?_, j, ?_, hn.symm⟩
      · exact hf.mem_toFinset.mpr hi
      · exact hg.mem_toFinset.mpr hj
    exact Set.Finite.subset (Finset.finite_toSet _) hsub
  have h : {n : ℕ | PowerSeries.coeff n (f * g) ≠ 0} ⊆ S := by
    intro n hn
    simp only [Set.mem_ofPred_eq] at hn
    by_contra hns
    simp only [S, Set.mem_ofPred_eq, not_exists, not_and] at hns
    have hzero : ∀ i, i ≤ n → (PowerSeries.coeff i) f * (PowerSeries.coeff (n - i)) g = 0 := by
      intro i hi
      by_cases hif : (PowerSeries.coeff i) f = 0
      · exact by rw [hif, zero_mul]
      · have hig : (PowerSeries.coeff (n - i)) g = 0 := by
          by_contra hig'
          have : n = i + (n - i) := (Nat.add_sub_cancel' hi).symm
          exact hns i hif (n - i) hig' this
        exact by rw [hig, mul_zero]
    apply hn
    rw [PowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro ⟨i, j⟩ hij
    simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hij
    have hi : i ≤ n := by omega
    have hj : j = n - i := by omega
    have := hzero i hi
    simp only at this ⊢
    rw [hj]
    exact this
  exact Set.Finite.subset hS h

end FPS
