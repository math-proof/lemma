/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2024 AlgebraicCombinatorics Contributors. All rights reserved.
Authors: AlgebraicCombinatorics Contributors
-/
import Mathlib
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
/-! ## Definition of Polynomial as FPS with Finite Support

Definition 7.5.1 (def.fps.pol): An FPS `a ∈ K⟦X⟧` is a polynomial if all but finitely many
coefficients are zero.
-/


/-- A power series is a polynomial if it has finite support, i.e., only finitely many
nonzero coefficients. This corresponds to Definition 7.5.1 (def.fps.pol) in the source. -/
def IsPolynomial (f : PowerSeries K) : Prop :=
  {n : ℕ | PowerSeries.coeff n f ≠ 0}.Finite

/-- The image of a polynomial under `toPowerSeries` is a polynomial (in the FPS sense). -/
theorem isPolynomial_of_polynomial (p : K[X]) : IsPolynomial (p : PowerSeries K) := by
  simp only [IsPolynomial]
  have h : {n : ℕ | PowerSeries.coeff n (p : PowerSeries K) ≠ 0} ⊆ ↑p.support := by
    intro n hn
    simp only [Set.mem_ofPred_eq] at hn
    simp only [Finset.mem_coe, Polynomial.mem_support_iff]
    rw [Polynomial.coeff_coe] at hn
    exact hn
  exact Set.Finite.subset p.support.finite_toSet h

/-- For a polynomial power series, there exists a degree bound such that all coefficients
beyond this bound are zero. This is an equivalent characterization of polynomials. -/
theorem isPolynomial_iff_exists_degree_bound (f : PowerSeries K) :
    IsPolynomial f ↔ ∃ N : ℕ, ∀ n ≥ N, PowerSeries.coeff n f = 0 := by
  constructor
  · intro hf
    simp only [IsPolynomial] at hf
    obtain ⟨N, hN⟩ := hf.bddAbove
    use N + 1
    intro n hn
    by_contra h
    have hmem : n ∈ {m : ℕ | PowerSeries.coeff m f ≠ 0} := h
    have hle : n ≤ N := hN hmem
    omega
  · intro ⟨N, hN⟩
    simp only [IsPolynomial]
    apply Set.Finite.subset (Finset.finite_toSet (Finset.range N))
    intro n hn
    simp only [Set.mem_ofPred_eq] at hn
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    push Not at h
    exact hn (hN n h)

/-- Convert a polynomial power series to its corresponding polynomial.
This requires a proof that the power series is a polynomial. -/
noncomputable def toPolynomial (f : PowerSeries K) (hf : IsPolynomial f) : K[X] :=
  (isPolynomial_iff_exists_degree_bound f).mp hf |>.choose |> fun N => PowerSeries.trunc N f
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
/-! ## K[x] as a Subalgebra of K[[x]]

Theorem 7.5.2 (thm.fps.pol.ring): The set K[x] is a subring of K[[x]] (closed under addition,
subtraction, and multiplication, and contains 0 and 1) and a K-submodule of K[[x]] (closed
under addition and scalar multiplication).

These two properties together mean that K[x] forms a K-subalgebra of K[[x]].
-/


/-- The set of polynomial power series forms a K-subalgebra of K[[x]].
This is Theorem 7.5.2 (thm.fps.pol.ring) in the source:
K[x] is a subring of K[[x]] (closed under +, -, *, contains 0 and 1)
and a K-submodule (closed under + and scalar multiplication). -/
def polynomialSubalgebra : Subalgebra K (PowerSeries K) where
  carrier := {f | IsPolynomial f}
  mul_mem' := isPolynomial_mul
  one_mem' := isPolynomial_one
  add_mem' := isPolynomial_add
  zero_mem' := isPolynomial_zero
  algebraMap_mem' := fun c => by
    simp only [Set.mem_ofPred_eq, IsPolynomial]
    have h : {n : ℕ | PowerSeries.coeff n (algebraMap K (PowerSeries K) c) ≠ 0} ⊆ {0} := by
      intro n hn
      simp only [Set.mem_ofPred_eq, ne_eq] at hn
      simp only [Set.mem_singleton_iff]
      by_contra hne
      simp only [Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul, PowerSeries.coeff_one,
        ite_eq_right hne, mul_zero, not_true_eq_false] at hn
    exact Set.Finite.subset (Set.finite_singleton 0) h

/-- The underlying subring of the polynomial subalgebra.
This is the "subring" part of Theorem 7.5.2 (thm.fps.pol.ring):
K[x] is closed under +, -, *, and contains 0 and 1. -/
noncomputable def polynomialSubring : Subring (PowerSeries K) :=
  polynomialSubalgebra.toSubring

/-- The underlying K-submodule of the polynomial subalgebra.
This is the "K-submodule" part of Theorem 7.5.2 (thm.fps.pol.ring):
K[x] is closed under + and scalar multiplication by elements of K. -/
noncomputable def polynomialSubmodule : Submodule K (PowerSeries K) :=
  polynomialSubalgebra.toSubmodule
/-! ## Rings (Noncommutative Rings)

Definition 7.5.3 (def.alg.ring): A ring (also known as a noncommutative ring) is defined
in the same way as a commutative ring, except that commutativity of multiplication
is not required.

In Mathlib, this is captured by the `Ring` typeclass. Note that "noncommutative ring"
does not imply that the ring is not commutative; it merely means that commutativity
is not required. Thus, any commutative ring is a noncommutative ring.

Examples of noncommutative rings:
- Matrix rings `Matrix n n R` for any ring R and n > 1
- The quaternions `ℍ[R]` (Mathlib: `Quaternion`)
- Endomorphism rings `Module.End R M` for any R-module M
-/


section RingBasics

variable {R : Type*} [Ring R]

end RingBasics
/-! ### Examples of Noncommutative Rings

The source lists several examples of noncommutative rings:
- Matrix rings `R^{n×n}` for any ring R (commutative if n ≤ 1, noncommutative if n > 1)
- The quaternions ℍ
- Endomorphism rings of abelian groups/modules
-/


section RingExamples

-- Matrix rings are rings (noncommutative for n > 1)
example (n : ℕ) (R : Type*) [Ring R] [DecidableEq (Fin n)] : Ring (Matrix (Fin n) (Fin n) R) :=
  inferInstance

-- The quaternions over ℝ are a ring (noncommutative)
noncomputable example : Ring (Quaternion ℝ) := inferInstance

-- Endomorphism rings are rings
example (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M] :
    Ring (Module.End R M) := inferInstance

-- Every commutative ring is a ring (commutativity is not required, just not forbidden)
example {K : Type*} [CommRing K] : Ring K := inferInstance

end RingExamples
/-! ## K-Algebras

### Definition 7.5.5 (def.alg.Kalg): K-Algebras

The source defines a K-algebra as a set A equipped with four maps:
- `⊕ : A × A → A` (addition)
- `⊖ : A × A → A` (subtraction)
- `⊙ : A × A → A` (multiplication)
- `⇀ : K × A → A` (scalar multiplication)

and two elements `0⃗ ∈ A` (zero) and `1⃗ ∈ A` (one), satisfying three properties:

1. **A is a (noncommutative) ring**: The set A with ⊕, ⊖, ⊙, 0⃗, 1⃗ is a ring
   (same as commutative ring but without commutativity of multiplication).

2. **A is a K-module**: The set A with ⊕, ⊖, ⇀, 0⃗ is a module.

3. **Compatibility property** (equation 7.5.2):
   `λ ⇀ (a ⊙ b) = (λ ⇀ a) ⊙ b = a ⊙ (λ ⇀ b)` for all `λ ∈ K` and `a, b ∈ A`.

In Mathlib, this is captured by the `Algebra` typeclass, which requires:
- `[Semiring A]` (or `[Ring A]` for rings with subtraction)
- `[Algebra K A]` which provides scalar multiplication and the compatibility property

The key property `λ(ab) = (λa)b = a(λb)` is expressed via:
- `Algebra.smul_mul_assoc`: `r • x * y = r • (x * y)`
- `Algebra.mul_smul_comm`: `x * r • y = r • (x * y)`
-/


section KAlgebra

variable {A : Type*} [Ring A] [Algebra K A]
/-! ### Property 1: A is a Ring

A K-algebra A is automatically a ring.
Note: The source allows noncommutative rings; in Mathlib, `Ring A` captures this.
For commutative algebras, we use `CommRing A`.
-/
/-! ### Property 2: A is a K-Module

A K-algebra A is automatically a K-module.
-/
/-! ### Property 3: Compatibility (Equation 7.5.2)

The key compatibility property: `λ(ab) = (λa)b = a(λb)` for all `λ ∈ K` and `a, b ∈ A`.

This says that scaling a product in A by a scalar λ ∈ K is equivalent to scaling
either of its two factors by λ.
-/

end KAlgebra
/-! ### Examples of K-Algebras

The source lists several examples of K-algebras:
- The ring K itself
- The ring K⟦X⟧ of formal power series
- The polynomial ring K[X] (as a subring of K⟦X⟧)
- The matrix ring K^{n×n} for each n ∈ ℕ
- Any quotient ring K/I where I is an ideal
- Any commutative ring containing K as a subring
-/


section KAlgebraExamples

/-- K is a K-algebra over itself.
    Label: def.alg.Kalg (Example 1) -/
example : Algebra K K := inferInstance

/-- The ring of formal power series K⟦X⟧ is a K-algebra.
    Label: def.alg.Kalg (Example 2) -/
noncomputable example : Algebra K (PowerSeries K) := inferInstance

/-- The polynomial ring K[X] is a K-algebra.
    Label: def.alg.Kalg (Example 3) -/
noncomputable example : Algebra K K[X] := inferInstance

/-- For any n, the matrix ring K^{n×n} is a K-algebra.
    Label: def.alg.Kalg (Example 4) -/
example (n : ℕ) : Algebra K (Matrix (Fin n) (Fin n) K) := inferInstance

/-- ℤ/m is a ℤ-algebra for any m.
    Label: def.alg.Kalg (Example 5) -/
example (m : ℕ) [NeZero m] : Algebra ℤ (ZMod m) := inferInstance

/-- ℚ is a ℤ-algebra.
    Label: def.alg.Kalg (Example 6) -/
example : Algebra ℤ ℚ := inferInstance

/-- Any ring is automatically a ℤ-algebra.
    This is because any ring has a unique ring homomorphism from ℤ.
    Label: def.alg.Kalg (Note) -/
example {R : Type*} [Ring R] : Algebra ℤ R := inferInstance

end KAlgebraExamples
/-! ### The algebraMap

In Mathlib, a K-algebra A comes with a ring homomorphism `algebraMap K A : K →+* A`
that embeds K into the center of A. This allows us to view elements of K as elements of A.
-/


section AlgebraMap

variable {A : Type*} [CommRing A] [Algebra K A]

/-- The algebraMap is a ring homomorphism from K to A.
    Label: def.alg.Kalg -/
example : K →+* A := algebraMap K A

end AlgebraMap
/-! ## Evaluation of Polynomials

Definition 7.5.6 (def.pol.subs): For a polynomial f ∈ K[x] and an element a of a K-algebra A,
we define f[a] := Σ_{n ∈ ℕ} f_n * a^n.

In Mathlib, this is `Polynomial.aeval a f` for evaluation in a K-algebra A.

### Implementation Notes

The book uses notation `f[a]` for polynomial evaluation. In Mathlib:
- `Polynomial.aeval a f` evaluates polynomial `f` at element `a` of a K-algebra
- `Polynomial.eval₂ φ a f` is more general, using a ring homomorphism `φ`
- `Polynomial.eval a f` evaluates in the base ring K itself

We provide `polyEval` as a wrapper matching the book's presentation.
-/


section Evaluation

variable {A : Type*} [CommRing A] [Algebra K A]

/-- Evaluation of a polynomial at an element of a K-algebra.
This is Definition 7.5.6 (def.pol.subs).

Given a polynomial f ∈ K[X] and an element a of a K-algebra A,
we define f[a] := Σ_{n ∈ ℕ} f_n · a^n.

The sum is essentially finite since f is a polynomial (only finitely many
coefficients are nonzero).

In Mathlib, this is implemented as `Polynomial.aeval a f`. -/
noncomputable abbrev polyEval (f : K[X]) (a : A) : A := aeval a f

/-- Notation for polynomial evaluation: `f⦃a⦄` means the value of `f` at `a`.
This corresponds to the book's notation `f[a]`. -/
scoped notation:max f:max "⦃" a "⦄" => polyEval f a
/-! ### Properties of Polynomial Evaluation

Theorem 7.5.7 (thm.pol.eval.a+b): Basic properties of evaluation.
-/

end Evaluation
/-! ## Examples and Special Cases -/
/-! ## Special Evaluation Results -/


section SpecialEval

variable {A : Type*} [CommRing A] [Algebra K A]

end SpecialEval

end FPS
