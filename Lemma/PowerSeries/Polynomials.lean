import Mathlib
import sympy.Basic
import sympy.series.formal.Polynomials


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
