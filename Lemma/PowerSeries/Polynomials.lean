import Mathlib
import Initialize.Tactic.Attr.Basic
import Notation.RingTheory.PowerSeries.Polynomials


section
-- ac-theorems


namespace FPS

open Polynomial PowerSeries

variable {K : Type*} [CommRing K]

/-- A power series is a polynomial iff its support (set of indices with nonzero coefficients)
is finite. -/
lemma isPolynomial_iff_finite_support (f : PowerSeries K) :
    IsPolynomial f ↔ {n : ℕ | PowerSeries.coeff n f ≠ 0}.Finite :=
  Iff.rfl

/-- A power series is a polynomial iff it equals the coercion of some polynomial.
This provides the key equivalence between `IsPolynomial` and Mathlib's `Polynomial` type. -/
lemma isPolynomial_iff_exists_polynomial (f : PowerSeries K) :
    IsPolynomial f ↔ ∃ p : K[X], f = p := by
  constructor
  · intro hf
    -- Use the degree bound characterization and truncation
    rw [isPolynomial_iff_exists_degree_bound] at hf
    obtain ⟨N, hN⟩ := hf
    use PowerSeries.trunc N f
    ext n
    rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
    split_ifs with hn
    · rfl
    · push Not at hn
      exact hN n hn
  · intro ⟨p, hp⟩
    rw [hp]
    exact isPolynomial_of_polynomial p

/-- The polynomial corresponding to a polynomial power series coerces back to the original.
This shows that `toPolynomial` is a left inverse of the coercion from polynomials. -/
lemma coe_toPolynomial (f : PowerSeries K) (hf : IsPolynomial f) :
    (toPolynomial f hf : PowerSeries K) = f := by
  simp only [toPolynomial]
  set N := (isPolynomial_iff_exists_degree_bound f).mp hf |>.choose
  have hN := (isPolynomial_iff_exists_degree_bound f).mp hf |>.choose_spec
  ext n
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  split_ifs with hn
  · rfl
  · push Not at hn
    exact (hN n hn).symm

/-- Converting a polynomial to a power series and back gives the original polynomial. -/
lemma toPolynomial_coe (p : K[X]) :
    toPolynomial (p : PowerSeries K) (isPolynomial_of_polynomial p) = p := by
  apply Polynomial.coe_injective K
  rw [coe_toPolynomial]

/-- The negation of a polynomial power series is a polynomial.
This is part of Theorem 7.5.2 (thm.fps.pol.ring). -/
lemma isPolynomial_neg {f : PowerSeries K} (hf : IsPolynomial f) : IsPolynomial (-f) := by
  simp only [IsPolynomial] at *
  convert hf using 1
  ext n
  simp only [Set.mem_ofPred_eq, map_neg, neg_ne_zero]

/-- The difference of two polynomial power series is a polynomial.
This is part of Theorem 7.5.2 (thm.fps.pol.ring). -/
lemma isPolynomial_sub {f g : PowerSeries K} (hf : IsPolynomial f) (hg : IsPolynomial g) :
    IsPolynomial (f - g) := by
  rw [sub_eq_add_neg]
  exact isPolynomial_add hf (isPolynomial_neg hg)

/-- Scalar multiplication of a polynomial power series is a polynomial.
This is part of Theorem 7.5.2 (thm.fps.pol.ring). -/
lemma isPolynomial_smul {f : PowerSeries K} (c : K) (hf : IsPolynomial f) :
    IsPolynomial (c • f) := by
  simp only [IsPolynomial] at *
  have h : {n : ℕ | PowerSeries.coeff n (c • f) ≠ 0} ⊆
      {n : ℕ | PowerSeries.coeff n f ≠ 0} := by
    intro n hn
    simp only [Set.mem_ofPred_eq, map_smul, smul_eq_mul, ne_eq] at hn
    simp only [Set.mem_ofPred_eq, ne_eq]
    intro hf'
    rw [hf', mul_zero] at hn
    exact hn rfl
  exact Set.Finite.subset hf h

/-- Membership in the polynomial subalgebra is equivalent to being a polynomial.
This is the characterization of K[x] from Theorem 7.5.2 (thm.fps.pol.ring). -/
@[simp]
lemma mem_polynomialSubalgebra (f : PowerSeries K) :
    f ∈ polynomialSubalgebra ↔ IsPolynomial f := Iff.rfl

/-- Membership in the polynomial subring is equivalent to being a polynomial.
This is the "subring" characterization from Theorem 7.5.2 (thm.fps.pol.ring). -/
@[simp]
lemma mem_polynomialSubring (f : PowerSeries K) :
    f ∈ polynomialSubring ↔ IsPolynomial f := Iff.rfl

/-- Membership in the polynomial submodule is equivalent to being a polynomial.
This is the "K-submodule" characterization from Theorem 7.5.2 (thm.fps.pol.ring). -/
@[simp]
lemma mem_polynomialSubmodule (f : PowerSeries K) :
    f ∈ polynomialSubmodule ↔ IsPolynomial f := Iff.rfl


section RingBasics

variable {R : Type*} [Ring R]

/-- **Associativity of addition**:
    `a + (b + c) = (a + b) + c` for all `a, b, c ∈ R`. -/
lemma ring_add_assoc (a b c : R) : a + (b + c) = (a + b) + c := (add_assoc a b c).symm

/-- **Commutativity of addition**:
    `a + b = b + a` for all `a, b ∈ R`.
    Note: Addition is always commutative, even in noncommutative rings. -/
lemma ring_add_comm (a b : R) : a + b = b + a := add_comm a b

/-- **Neutrality of zero**:
    `a + 0 = a` for all `a ∈ R`. -/
lemma ring_add_zero (a : R) : a + 0 = a := add_zero a

/-- **Neutrality of zero**:
    `0 + a = a` for all `a ∈ R`. -/
lemma ring_zero_add (a : R) : 0 + a = a := zero_add a

/-- **Existence of additive inverse**:
    `a + (-a) = 0` for all `a ∈ R`. -/
lemma ring_add_neg (a : R) : a + (-a) = 0 := add_neg_cancel a

/-- **Associativity of multiplication**:
    `a * (b * c) = (a * b) * c` for all `a, b, c ∈ R`. -/
lemma ring_mul_assoc (a b c : R) : a * (b * c) = (a * b) * c := (mul_assoc a b c).symm

/-- **Left distributivity**:
    `a * (b + c) = a * b + a * c` for all `a, b, c ∈ R`. -/
lemma ring_left_distrib (a b c : R) : a * (b + c) = a * b + a * c := mul_add a b c

/-- **Right distributivity**:
    `(a + b) * c = a * c + b * c` for all `a, b, c ∈ R`. -/
lemma ring_right_distrib (a b c : R) : (a + b) * c = a * c + b * c := add_mul a b c

/-- **Neutrality of one**:
    `a * 1 = a` for all `a ∈ R`. -/
lemma ring_mul_one (a : R) : a * 1 = a := mul_one a

/-- **Neutrality of one**:
    `1 * a = a` for all `a ∈ R`. -/
lemma ring_one_mul (a : R) : 1 * a = a := one_mul a

/-- **Annihilation** (Ring property):
    `a * 0 = 0` for all `a ∈ R`. -/
lemma ring_mul_zero (a : R) : a * 0 = 0 := mul_zero a

/-- **Annihilation** (Ring property):
    `0 * a = 0` for all `a ∈ R`. -/
lemma ring_zero_mul (a : R) : 0 * a = 0 := zero_mul a

end RingBasics


section RingExamples

end RingExamples


section KAlgebra

variable {A : Type*} [Ring A] [Algebra K A]


/-- A K-algebra is a ring: addition is commutative.
    Label: def.alg.Kalg (Property 1) -/
lemma kalg_add_comm (a b : A) : a + b = b + a := add_comm a b

/-- A K-algebra is a ring: addition is associative.
    Label: def.alg.Kalg (Property 1) -/
lemma kalg_add_assoc (a b c : A) : a + (b + c) = (a + b) + c := (add_assoc a b c).symm

/-- A K-algebra is a ring: zero is the additive identity.
    Label: def.alg.Kalg (Property 1) -/
lemma kalg_add_zero (a : A) : a + 0 = a := add_zero a

/-- A K-algebra is a ring: multiplication is associative.
    Label: def.alg.Kalg (Property 1) -/
lemma kalg_mul_assoc (a b c : A) : a * (b * c) = (a * b) * c := (mul_assoc a b c).symm

/-- A K-algebra is a ring: left distributivity.
    Label: def.alg.Kalg (Property 1) -/
lemma kalg_left_distrib (a b c : A) : a * (b + c) = a * b + a * c := mul_add a b c

/-- A K-algebra is a ring: right distributivity.
    Label: def.alg.Kalg (Property 1) -/
lemma kalg_right_distrib (a b c : A) : (a + b) * c = a * c + b * c := add_mul a b c

/-- A K-algebra is a ring: one is the multiplicative identity.
    Label: def.alg.Kalg (Property 1) -/
lemma kalg_mul_one (a : A) : a * 1 = a := mul_one a

/-- A K-algebra is a ring: one is the multiplicative identity (left).
    Label: def.alg.Kalg (Property 1) -/
lemma kalg_one_mul (a : A) : 1 * a = a := one_mul a


/-- A K-algebra is a K-module: scalar multiplication is associative.
    Label: def.alg.Kalg (Property 2) -/
lemma kalg_smul_assoc (u v : K) (a : A) : u • (v • a) = (u * v) • a := by rw [mul_smul]

/-- A K-algebra is a K-module: scalar multiplication distributes over addition (left).
    Label: def.alg.Kalg (Property 2) -/
lemma kalg_smul_add (u : K) (a b : A) : u • (a + b) = u • a + u • b := smul_add u a b

/-- A K-algebra is a K-module: scalar multiplication distributes over addition (right).
    Label: def.alg.Kalg (Property 2) -/
lemma kalg_add_smul (u v : K) (a : A) : (u + v) • a = u • a + v • a := add_smul u v a

/-- A K-algebra is a K-module: 1 acts as identity.
    Label: def.alg.Kalg (Property 2) -/
lemma kalg_one_smul (a : A) : (1 : K) • a = a := one_smul K a

/-- A K-algebra is a K-module: 0 annihilates.
    Label: def.alg.Kalg (Property 2) -/
lemma kalg_zero_smul (a : A) : (0 : K) • a = 0 := zero_smul K a

/-- A K-algebra is a K-module: scalar multiplication by zero element gives zero.
    Label: def.alg.Kalg (Property 2) -/
lemma kalg_smul_zero (u : K) : u • (0 : A) = 0 := smul_zero u


/-- The compatibility property for K-algebras: `λ(ab) = (λa)b`.
    This is equation (7.5.2) in the source.
    Label: def.alg.Kalg (Property 3) -/
lemma kalg_smul_mul_assoc (c : K) (a b : A) : c • (a * b) = (c • a) * b :=
  (Algebra.smul_mul_assoc c a b).symm

/-- The compatibility property for K-algebras: `λ(ab) = a(λb)`.
    This is equation (7.5.2) in the source.
    Label: def.alg.Kalg (Property 3) -/
lemma kalg_mul_smul_comm (c : K) (a b : A) : c • (a * b) = a * (c • b) :=
  (Algebra.mul_smul_comm c a b).symm

/-- Combined compatibility: `(λa)b = a(λb)`.
    Follows from the two parts of equation (7.5.2).
    Label: def.alg.Kalg (Property 3) -/
lemma kalg_smul_mul_eq_mul_smul (c : K) (a b : A) : (c • a) * b = a * (c • b) := by
  rw [← kalg_smul_mul_assoc, kalg_mul_smul_comm]

end KAlgebra


section KAlgebraExamples

end KAlgebraExamples


section AlgebraMap

variable {A : Type*} [CommRing A] [Algebra K A]

/-- algebraMap preserves zero. -/
lemma algebraMap_zero : algebraMap K A 0 = 0 := map_zero (algebraMap K A)

/-- algebraMap preserves one. -/
lemma algebraMap_one : algebraMap K A 1 = 1 := map_one (algebraMap K A)

/-- algebraMap preserves addition. -/
lemma algebraMap_add (a b : K) : algebraMap K A (a + b) = algebraMap K A a + algebraMap K A b :=
  map_add (algebraMap K A) a b

/-- algebraMap preserves multiplication. -/
lemma algebraMap_mul (a b : K) : algebraMap K A (a * b) = algebraMap K A a * algebraMap K A b :=
  map_mul (algebraMap K A) a b

/-- Elements in the image of algebraMap commute with all elements of A.
    This is a key property: algebraMap K A lands in the center of A. -/
lemma algebraMap_commutes (r : K) (x : A) : algebraMap K A r * x = x * algebraMap K A r :=
  Algebra.commutes r x

/-- Scalar multiplication is related to algebraMap:
    `r • x = algebraMap K A r * x`. -/
lemma smul_eq_algebraMap_mul (r : K) (x : A) : r • x = algebraMap K A r * x :=
  Algebra.smul_def r x

end AlgebraMap


section Evaluation

variable {A : Type*} [CommRing A] [Algebra K A]

/-- Evaluation of a polynomial at an element of a K-algebra equals the sum Σ f_n · a^n.
This is the explicit formula from Definition 7.5.6 (def.pol.subs). -/
lemma eval_def (f : K[X]) (a : A) :
    f⦃a⦄ = f.sum fun n c => algebraMap K A c * a ^ n := by
  rw [polyEval, aeval_def, eval₂_eq_sum]

/-- The evaluation f[a] can be written as a finite sum over the support of f.
This makes explicit that the sum in Definition 7.5.6 is essentially finite. -/
lemma eval_eq_finsum (f : K[X]) (a : A) :
    f⦃a⦄ = ∑ n ∈ f.support, algebraMap K A (f.coeff n) * a ^ n := by
  rw [polyEval, aeval_def, eval₂_eq_sum, Polynomial.sum]

/-- Alternative formulation: f[a] = Σ_{n=0}^{deg f} f_n · a^n.
This shows that the sum can be taken up to the degree. -/
lemma eval_eq_sum_range (f : K[X]) (a : A) :
    f⦃a⦄ = ∑ n ∈ Finset.range (f.natDegree + 1), algebraMap K A (f.coeff n) * a ^ n := by
  rw [polyEval, aeval_def, eval₂_eq_sum_range]


/-- (f + g)[a] = f[a] + g[a].
This is Theorem 7.5.7(a) in the source. -/
lemma eval_add' (f g : K[X]) (a : A) :
    (f + g)⦃a⦄ = f⦃a⦄ + g⦃a⦄ :=
  map_add (aeval a) f g

/-- (f * g)[a] = f[a] * g[a].
This is Theorem 7.5.7(a) in the source. -/
lemma eval_mul' (f g : K[X]) (a : A) :
    (f * g)⦃a⦄ = f⦃a⦄ * g⦃a⦄ :=
  map_mul (aeval a) f g

/-- (c · f)[a] = c · f[a].
This is Theorem 7.5.7(b) in the source. -/
lemma eval_smul' (f : K[X]) (c : K) (a : A) :
    (c • f)⦃a⦄ = c • f⦃a⦄ :=
  map_smul (aeval a) c f

/-- C(c)[a] = c · 1_A.
This is Theorem 7.5.7(c) in the source. -/
lemma eval_C' (c : K) (a : A) :
    (Polynomial.C c)⦃a⦄ = algebraMap K A c :=
  aeval_C a c

/-- X[a] = a.
This is Theorem 7.5.7(d) in the source. -/
lemma eval_X' (a : A) :
    (Polynomial.X : K[X])⦃a⦄ = a :=
  aeval_X a

/-- X^i[a] = a^i.
This is Theorem 7.5.7(e) in the source. -/
lemma eval_X_pow' (a : A) (i : ℕ) :
    ((Polynomial.X : K[X]) ^ i)⦃a⦄ = a ^ i := by
  simp only [polyEval, map_pow, aeval_X]

/-- f[g[a]] = (f ∘ g)[a], where f ∘ g denotes composition of polynomials.
This is Theorem 7.5.7(f) in the source. -/
lemma eval_comp' (f g : K[X]) (a : A) :
    f⦃g⦃a⦄⦄ = (f.comp g)⦃a⦄ := by
  rw [polyEval, polyEval, polyEval, aeval_comp]

end Evaluation


/-- The polynomial X is a polynomial (in the FPS sense). -/
@[simp]
lemma isPolynomial_X : IsPolynomial (PowerSeries.X : PowerSeries K) := by
  simp only [IsPolynomial]
  have h : {n : ℕ | PowerSeries.coeff n (PowerSeries.X : PowerSeries K) ≠ 0} ⊆ {1} := by
    intro n hn
    simp only [Set.mem_ofPred_eq, PowerSeries.coeff_X, ne_eq] at hn
    simp only [Set.mem_singleton_iff]
    by_contra hne
    rw [ite_eq_right hne] at hn
    exact hn rfl
  exact Set.Finite.subset (Set.finite_singleton 1) h

/-- Any constant is a polynomial (in the FPS sense). -/
@[simp]
lemma isPolynomial_C (c : K) : IsPolynomial (PowerSeries.C c) := by
  simp only [IsPolynomial]
  have h : {n : ℕ | PowerSeries.coeff n (PowerSeries.C c) ≠ 0} ⊆ {0} := by
    intro n hn
    simp only [Set.mem_ofPred_eq, ne_eq] at hn
    simp only [Set.mem_singleton_iff]
    by_contra hne
    rw [PowerSeries.coeff_C, ite_eq_right hne] at hn
    exact hn rfl
  exact Set.Finite.subset (Set.finite_singleton 0) h


section SpecialEval

variable {A : Type*} [CommRing A] [Algebra K A]

/-- f[x] = f, i.e., evaluating at the indeterminate gives back the polynomial.
This is noted after Definition 7.5.6 in the source. -/
lemma eval_X_eq_self (f : K[X]) :
    f⦃(Polynomial.X : K[X])⦄ = f := by
  have h := Polynomial.aeval_X_left (R := K)
  simp only [AlgHom.ext_iff, AlgHom.id_apply] at h
  exact h f

/-- f[0] = f₀, i.e., evaluating at 0 gives the constant term.
This is noted after Definition 7.5.6 in the source. -/
lemma eval_zero_eq_coeff_zero (f : K[X]) :
    f⦃(0 : A)⦄ = algebraMap K A (f.coeff 0) := by
  simp only [polyEval, aeval_def, eval₂_at_zero]

/-- f[1] = sum of all coefficients of f.
This is noted after Definition 7.5.6 in the source. -/
lemma eval_one_eq_sum_coeffs (f : K[X]) :
    f⦃(1 : A)⦄ = algebraMap K A (f.sum fun _ c => c) := by
  rw [polyEval, aeval_def, eval₂_at_one, Polynomial.eval_eq_sum]
  simp only [one_pow, mul_one]

end SpecialEval

end FPS
end


/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma is_polynomial_iff_finite_support_iff
  [CommRing K]
-- given
  (f : PowerSeries K) :
-- imply
  FPS.IsPolynomial f ↔ {n : ℕ | PowerSeries.coeff n f ≠ 0}.Finite := by
-- proof
  apply FPS.isPolynomial_iff_finite_support f

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma is_polynomial_of_polynomial_is
  [CommRing K]
-- given
  (p : Polynomial K) :
-- imply
  FPS.IsPolynomial (p : PowerSeries K) := by
-- proof
  apply FPS.isPolynomial_of_polynomial p

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma is_polynomial_iff_exists_degree_bound_iff
  [CommRing K]
-- given
  (f : PowerSeries K) :
-- imply
  FPS.IsPolynomial f ↔ ∃ N : ℕ, ∀ n ≥ N, PowerSeries.coeff n f = 0 := by
-- proof
  apply FPS.isPolynomial_iff_exists_degree_bound f

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma is_polynomial_iff_exists_polynomial_iff
  [CommRing K]
-- given
  (f : PowerSeries K) :
-- imply
  FPS.IsPolynomial f ↔ ∃ p : Polynomial K, f = (p : PowerSeries K) := by
-- proof
  apply FPS.isPolynomial_iff_exists_polynomial f

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma coe_to_polynomial_eq
  [CommRing K]
-- given
  (f : PowerSeries K)
  (hf : FPS.IsPolynomial f) :
-- imply
  (FPS.toPolynomial f hf : PowerSeries K) = f := by
-- proof
  apply FPS.coe_toPolynomial f hf

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma to_polynomial_coe_eq
  [CommRing K]
-- given
  (p : Polynomial K) :
-- imply
  FPS.toPolynomial (p : PowerSeries K) (FPS.isPolynomial_of_polynomial p) = p := by
-- proof
  apply FPS.toPolynomial_coe p

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma is_polynomial_zero_is
  [CommRing K] :
-- imply
  FPS.IsPolynomial (0 : PowerSeries K) := by
-- proof
  apply FPS.isPolynomial_zero

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma is_polynomial_one_is
  [CommRing K] :
-- imply
  FPS.IsPolynomial (1 : PowerSeries K) := by
-- proof
  apply FPS.isPolynomial_one

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma is_polynomial_add_is
  [CommRing K]
-- given
  (f g : PowerSeries K)
  (hf : FPS.IsPolynomial f)
  (hg : FPS.IsPolynomial g) :
-- imply
  FPS.IsPolynomial (f + g) := by
-- proof
  apply FPS.isPolynomial_add hf hg

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma is_polynomial_neg_is
  [CommRing K]
-- given
  (f : PowerSeries K)
  (hf : FPS.IsPolynomial f) :
-- imply
  FPS.IsPolynomial (-f) := by
-- proof
  apply FPS.isPolynomial_neg hf

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma is_polynomial_sub_is
  [CommRing K]
-- given
  (f g : PowerSeries K)
  (hf : FPS.IsPolynomial f)
  (hg : FPS.IsPolynomial g) :
-- imply
  FPS.IsPolynomial (f - g) := by
-- proof
  apply FPS.isPolynomial_sub hf hg

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma is_polynomial_mul_is
  [CommRing K]
-- given
  (f g : PowerSeries K)
  (hf : FPS.IsPolynomial f)
  (hg : FPS.IsPolynomial g) :
-- imply
  FPS.IsPolynomial (f * g) := by
-- proof
  apply FPS.isPolynomial_mul hf hg

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma is_polynomial_smul_is
  [CommRing K]
-- given
  (f : PowerSeries K)
  (hf : FPS.IsPolynomial f)
  (c : K) :
-- imply
  FPS.IsPolynomial (c • f) := by
-- proof
  apply FPS.isPolynomial_smul c hf

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma mem_polynomial_subalgebra_iff
  [CommRing K]
-- given
  (f : PowerSeries K) :
-- imply
  f ∈ FPS.polynomialSubalgebra ↔ FPS.IsPolynomial f := by
-- proof
  apply FPS.mem_polynomialSubalgebra f

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma mem_polynomial_subring_iff
  [CommRing K]
-- given
  (f : PowerSeries K) :
-- imply
  f ∈ FPS.polynomialSubring ↔ FPS.IsPolynomial f := by
-- proof
  apply FPS.mem_polynomialSubring f

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma mem_polynomial_submodule_iff
  [CommRing K]
-- given
  (f : PowerSeries K) :
-- imply
  f ∈ FPS.polynomialSubmodule ↔ FPS.IsPolynomial f := by
-- proof
  apply FPS.mem_polynomialSubmodule f

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma ring_add_assoc_eq
  [Ring R]
-- given
  (a b c : R) :
-- imply
  a + (b + c) = (a + b) + c := by
-- proof
  apply FPS.ring_add_assoc a b c

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma ring_add_comm_eq
  [Ring R]
-- given
  (a b : R) :
-- imply
  a + b = b + a := by
-- proof
  apply FPS.ring_add_comm a b

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma ring_add_zero_eq
  [Ring R]
-- given
  (a : R) :
-- imply
  a + 0 = a := by
-- proof
  apply FPS.ring_add_zero a

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma ring_zero_add_eq
  [Ring R]
-- given
  (a : R) :
-- imply
  0 + a = a := by
-- proof
  apply FPS.ring_zero_add a

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma ring_add_neg_eq
  [Ring R]
-- given
  (a : R) :
-- imply
  a + (-a) = 0 := by
-- proof
  apply FPS.ring_add_neg a

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma ring_mul_assoc_eq
  [Ring R]
-- given
  (a b c : R) :
-- imply
  a * (b * c) = (a * b) * c := by
-- proof
  apply FPS.ring_mul_assoc a b c

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma ring_left_distrib_eq
  [Ring R]
-- given
  (a b c : R) :
-- imply
  a * (b + c) = a * b + a * c := by
-- proof
  apply FPS.ring_left_distrib a b c

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma ring_right_distrib_eq
  [Ring R]
-- given
  (a b c : R) :
-- imply
  (a + b) * c = a * c + b * c := by
-- proof
  apply FPS.ring_right_distrib a b c

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma ring_mul_one_eq
  [Ring R]
-- given
  (a : R) :
-- imply
  a * 1 = a := by
-- proof
  apply FPS.ring_mul_one a

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma ring_one_mul_eq
  [Ring R]
-- given
  (a : R) :
-- imply
  1 * a = a := by
-- proof
  apply FPS.ring_one_mul a

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma ring_mul_zero_eq
  [Ring R]
-- given
  (a : R) :
-- imply
  a * 0 = 0 := by
-- proof
  apply FPS.ring_mul_zero a

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma ring_zero_mul_eq
  [Ring R]
-- given
  (a : R) :
-- imply
  0 * a = 0 := by
-- proof
  apply FPS.ring_zero_mul a

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma kalg_add_comm_eq
  [CommRing K] [Ring A] [Algebra K A]
-- given
  (a b : A) :
-- imply
  a + b = b + a := by
-- proof
  apply FPS.kalg_add_comm a b

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma kalg_add_assoc_eq
  [CommRing K] [Ring A] [Algebra K A]
-- given
  (a b c : A) :
-- imply
  a + (b + c) = (a + b) + c := by
-- proof
  apply FPS.kalg_add_assoc a b c

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma kalg_add_zero_eq
  [CommRing K] [Ring A] [Algebra K A]
-- given
  (a : A) :
-- imply
  a + 0 = a := by
-- proof
  apply FPS.kalg_add_zero a

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma kalg_mul_assoc_eq
  [CommRing K] [Ring A] [Algebra K A]
-- given
  (a b c : A) :
-- imply
  a * (b * c) = (a * b) * c := by
-- proof
  apply FPS.kalg_mul_assoc a b c

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma kalg_left_distrib_eq
  [CommRing K] [Ring A] [Algebra K A]
-- given
  (a b c : A) :
-- imply
  a * (b + c) = a * b + a * c := by
-- proof
  apply FPS.kalg_left_distrib a b c

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma kalg_right_distrib_eq
  [CommRing K] [Ring A] [Algebra K A]
-- given
  (a b c : A) :
-- imply
  (a + b) * c = a * c + b * c := by
-- proof
  apply FPS.kalg_right_distrib a b c

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma kalg_mul_one_eq
  [CommRing K] [Ring A] [Algebra K A]
-- given
  (a : A) :
-- imply
  a * 1 = a := by
-- proof
  apply FPS.kalg_mul_one a

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma kalg_one_mul_eq
  [CommRing K] [Ring A] [Algebra K A]
-- given
  (a : A) :
-- imply
  1 * a = a := by
-- proof
  apply FPS.kalg_one_mul a

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma kalg_smul_assoc_eq
  [CommRing K] [Ring A] [Algebra K A]
-- given
  (u v : K)
  (a : A) :
-- imply
  u • (v • a) = (u * v) • a := by
-- proof
  apply FPS.kalg_smul_assoc u v a

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma kalg_smul_add_eq
  [CommRing K] [Ring A] [Algebra K A]
-- given
  (u : K)
  (a b : A) :
-- imply
  u • (a + b) = u • a + u • b := by
-- proof
  apply FPS.kalg_smul_add u a b

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma kalg_add_smul_eq
  [CommRing K] [Ring A] [Algebra K A]
-- given
  (u v : K)
  (a : A) :
-- imply
  (u + v) • a = u • a + v • a := by
-- proof
  apply FPS.kalg_add_smul u v a

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma kalg_one_smul_eq
  [CommRing K] [Ring A] [Algebra K A]
-- given
  (a : A) :
-- imply
  (1 : K) • a = a := by
-- proof
  apply FPS.kalg_one_smul a

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma kalg_zero_smul_eq
  [CommRing K] [Ring A] [Algebra K A]
-- given
  (a : A) :
-- imply
  (0 : K) • a = 0 := by
-- proof
  apply FPS.kalg_zero_smul a

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma kalg_smul_zero_eq
  [CommRing K] [Ring A] [Algebra K A]
-- given
  (u : K) :
-- imply
  u • (0 : A) = 0 := by
-- proof
  apply FPS.kalg_smul_zero u

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma kalg_smul_mul_assoc_eq
  [CommRing K] [Ring A] [Algebra K A]
-- given
  (c : K)
  (a b : A) :
-- imply
  c • (a * b) = (c • a) * b := by
-- proof
  apply FPS.kalg_smul_mul_assoc c a b

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma kalg_mul_smul_comm_eq
  [CommRing K] [Ring A] [Algebra K A]
-- given
  (c : K)
  (a b : A) :
-- imply
  c • (a * b) = a * (c • b) := by
-- proof
  apply FPS.kalg_mul_smul_comm c a b

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma kalg_smul_mul_eq_mul_smul_eq
  [CommRing K] [Ring A] [Algebra K A]
-- given
  (c : K)
  (a b : A) :
-- imply
  (c • a) * b = a * (c • b) := by
-- proof
  apply FPS.kalg_smul_mul_eq_mul_smul c a b

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma algebra_map_zero_eq
  [CommRing K] [CommRing A] [Algebra K A] :
-- imply
  algebraMap K A 0 = 0 := by
-- proof
  apply FPS.algebraMap_zero

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma algebra_map_one_eq
  [CommRing K] [CommRing A] [Algebra K A] :
-- imply
  algebraMap K A 1 = 1 := by
-- proof
  apply FPS.algebraMap_one

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma algebra_map_add_eq
  [CommRing K] [CommRing A] [Algebra K A]
-- given
  (a b : K) :
-- imply
  algebraMap K A (a + b) = algebraMap K A a + algebraMap K A b := by
-- proof
  apply FPS.algebraMap_add a b

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma algebra_map_mul_eq
  [CommRing K] [CommRing A] [Algebra K A]
-- given
  (a b : K) :
-- imply
  algebraMap K A (a * b) = algebraMap K A a * algebraMap K A b := by
-- proof
  apply FPS.algebraMap_mul a b

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma algebra_map_commutes_eq
  [CommRing K] [CommRing A] [Algebra K A]
-- given
  (r : K)
  (x : A) :
-- imply
  algebraMap K A r * x = x * algebraMap K A r := by
-- proof
  apply FPS.algebraMap_commutes r x

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma smul_eq_algebra_map_mul_eq
  [CommRing K] [CommRing A] [Algebra K A]
-- given
  (r : K)
  (x : A) :
-- imply
  r • x = algebraMap K A r * x := by
-- proof
  apply FPS.smul_eq_algebraMap_mul r x

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma eval_def_eq
  [CommRing K] [CommRing A] [Algebra K A]
-- given
  (f : Polynomial K)
  (a : A) :
-- imply
  FPS.polyEval f a = f.sum fun n c => algebraMap K A c * a ^ n := by
-- proof
  apply FPS.eval_def f a

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma eval_eq_finsum_eq
  [CommRing K] [CommRing A] [Algebra K A]
-- given
  (f : Polynomial K)
  (a : A) :
-- imply
  FPS.polyEval f a = ∑ n ∈ f.support, algebraMap K A (f.coeff n) * a ^ n := by
-- proof
  apply FPS.eval_eq_finsum f a

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma eval_eq_sum_range_eq
  [CommRing K] [CommRing A] [Algebra K A]
-- given
  (f : Polynomial K)
  (a : A) :
-- imply
  FPS.polyEval f a = ∑ n ∈ Finset.range (f.natDegree + 1), algebraMap K A (f.coeff n) * a ^ n := by
-- proof
  apply FPS.eval_eq_sum_range f a

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma eval_add'_eq
  [CommRing K] [CommRing A] [Algebra K A]
-- given
  (f g : Polynomial K)
  (a : A) :
-- imply
  FPS.polyEval (f + g) a = FPS.polyEval f a + FPS.polyEval g a := by
-- proof
  apply FPS.eval_add' f g a

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma eval_mul'_eq
  [CommRing K] [CommRing A] [Algebra K A]
-- given
  (f g : Polynomial K)
  (a : A) :
-- imply
  FPS.polyEval (f * g) a = FPS.polyEval f a * FPS.polyEval g a := by
-- proof
  apply FPS.eval_mul' f g a

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma eval_smul'_eq
  [CommRing K] [CommRing A] [Algebra K A]
-- given
  (f : Polynomial K)
  (c : K)
  (a : A) :
-- imply
  FPS.polyEval (c • f) a = c • FPS.polyEval f a := by
-- proof
  apply FPS.eval_smul' f c a

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma eval_c'_eq
  [CommRing K] [CommRing A] [Algebra K A]
-- given
  (c : K)
  (a : A) :
-- imply
  FPS.polyEval (Polynomial.C c) a = algebraMap K A c := by
-- proof
  apply FPS.eval_C' c a

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma eval_x'_eq
  [CommRing K] [CommRing A] [Algebra K A]
-- given
  (a : A) :
-- imply
  FPS.polyEval (Polynomial.X : Polynomial K) a = a := by
-- proof
  apply FPS.eval_X' a

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma eval_x_pow'_eq
  [CommRing K] [CommRing A] [Algebra K A]
-- given
  (a : A)
  (i : ℕ) :
-- imply
  FPS.polyEval ((Polynomial.X : Polynomial K) ^ i) a = a ^ i := by
-- proof
  apply FPS.eval_X_pow' a i

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma eval_comp'_eq
  [CommRing K] [CommRing A] [Algebra K A]
-- given
  (f g : Polynomial K)
  (a : A) :
-- imply
  FPS.polyEval f (FPS.polyEval g a) = FPS.polyEval (f.comp g) a := by
-- proof
  apply FPS.eval_comp' f g a

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma is_polynomial_x_is
  [CommRing K] :
-- imply
  FPS.IsPolynomial (PowerSeries.X : PowerSeries K) := by
-- proof
  apply FPS.isPolynomial_X

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma is_polynomial_c_is
  [CommRing K]
-- given
  (c : K) :
-- imply
  FPS.IsPolynomial (PowerSeries.C c) := by
-- proof
  apply FPS.isPolynomial_C c

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma eval_x_eq_self_eq
  [CommRing K]
-- given
  (f : Polynomial K) :
-- imply
  FPS.polyEval f (Polynomial.X : Polynomial K) = f := by
-- proof
  apply FPS.eval_X_eq_self f

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma eval_zero_eq_coeff_zero_eq
  [CommRing K] [CommRing A] [Algebra K A]
-- given
  (f : Polynomial K) :
-- imply
  FPS.polyEval f (0 : A) = algebraMap K A (f.coeff 0) := by
-- proof
  apply FPS.eval_zero_eq_coeff_zero f

/--
[Polynomials](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Polynomials.lean)
-/
@[path]
private lemma eval_one_eq_sum_coeffs_eq
  [CommRing K] [CommRing A] [Algebra K A]
-- given
  (f : Polynomial K) :
-- imply
  FPS.polyEval f (1 : A) = algebraMap K A (f.sum fun _ c => c) := by
-- proof
  apply FPS.eval_one_eq_sum_coeffs f


-- created on 2026-10-11
