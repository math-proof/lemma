import Mathlib
import sympy.Basic
import sympy.series.formal.CommutativeRings
open AlgebraicCombinatorics.FPS
open scoped BigOperators


/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma commRing_add_comm
  [CommRing K]
-- given
  (a b : K) :
-- imply
  a + b = b + a := by
-- proof
  apply AlgebraicCombinatorics.FPS.commRing_add_comm a b

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma commRing_add_assoc
  [CommRing K]
-- given
  (a b c : K) :
-- imply
  a + (b + c) = (a + b) + c := by
-- proof
  apply AlgebraicCombinatorics.FPS.commRing_add_assoc a b c

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma commRing_add_zero
  [CommRing K]
-- given
  (a : K) :
-- imply
  a + 0 = a := by
-- proof
  apply AlgebraicCombinatorics.FPS.commRing_add_zero a

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma commRing_zero_add
  [CommRing K]
-- given
  (a : K) :
-- imply
  0 + a = a := by
-- proof
  apply AlgebraicCombinatorics.FPS.commRing_zero_add a

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma commRing_sub_iff_add
  [CommRing K]
-- given
  (a b c : K) :
-- imply
  a + b = c ↔ a = c - b := by
-- proof
  apply AlgebraicCombinatorics.FPS.commRing_sub_iff_add a b c

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma commRing_mul_comm
  [CommRing K]
-- given
  (a b : K) :
-- imply
  a * b = b * a := by
-- proof
  apply AlgebraicCombinatorics.FPS.commRing_mul_comm a b

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma commRing_mul_assoc
  [CommRing K]
-- given
  (a b c : K) :
-- imply
  a * (b * c) = (a * b) * c := by
-- proof
  apply AlgebraicCombinatorics.FPS.commRing_mul_assoc a b c

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma commRing_left_distrib
  [CommRing K]
-- given
  (a b c : K) :
-- imply
  a * (b + c) = a * b + a * c := by
-- proof
  apply AlgebraicCombinatorics.FPS.commRing_left_distrib a b c

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma commRing_right_distrib
  [CommRing K]
-- given
  (a b c : K) :
-- imply
  (a + b) * c = a * c + b * c := by
-- proof
  apply AlgebraicCombinatorics.FPS.commRing_right_distrib a b c

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma commRing_mul_one
  [CommRing K]
-- given
  (a : K) :
-- imply
  a * 1 = a := by
-- proof
  apply AlgebraicCombinatorics.FPS.commRing_mul_one a

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma commRing_one_mul
  [CommRing K]
-- given
  (a : K) :
-- imply
  1 * a = a := by
-- proof
  apply AlgebraicCombinatorics.FPS.commRing_one_mul a

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma commRing_mul_zero
  [CommRing K]
-- given
  (a : K) :
-- imply
  a * 0 = 0 := by
-- proof
  apply AlgebraicCombinatorics.FPS.commRing_mul_zero a

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma commRing_zero_mul
  [CommRing K]
-- given
  (a : K) :
-- imply
  0 * a = 0 := by
-- proof
  apply AlgebraicCombinatorics.FPS.commRing_zero_mul a

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma neg_add_distrib
  [CommRing K]
-- given
  (a b : K) :
-- imply
  -(a + b) = -a + -b := by
-- proof
  apply AlgebraicCombinatorics.FPS.neg_add_distrib a b

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma neg_neg_eq
  [CommRing K]
-- given
  (a : K) :
-- imply
  -(-a) = a := by
-- proof
  apply AlgebraicCombinatorics.FPS.neg_neg_eq a

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma add_zsmul_distrib
  [CommRing K]
-- given
  (a : K)
  (n m : ℤ) :
-- imply
  (n + m) • a = n • a + m • a := by
-- proof
  apply AlgebraicCombinatorics.FPS.add_zsmul_distrib a n m

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma mul_zsmul_assoc
  [CommRing K]
-- given
  (a : K)
  (n m : ℤ) :
-- imply
  (n * m) • a = n • (m • a) := by
-- proof
  apply AlgebraicCombinatorics.FPS.mul_zsmul_assoc a n m

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma mul_sub_distrib
  [CommRing K]
-- given
  (a b c : K) :
-- imply
  a * (b - c) = a * b - a * c := by
-- proof
  apply AlgebraicCombinatorics.FPS.mul_sub_distrib a b c

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma mul_pow_eq
  [CommRing K]
-- given
  (a b : K)
  (n : ℕ) :
-- imply
  (a * b) ^ n = a ^ n * b ^ n := by
-- proof
  apply AlgebraicCombinatorics.FPS.mul_pow_eq a b n

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma pow_add_eq
  [CommRing K]
-- given
  (a : K)
  (n m : ℕ) :
-- imply
  a ^ (n + m) = a ^ n * a ^ m := by
-- proof
  apply AlgebraicCombinatorics.FPS.pow_add_eq a n m

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma pow_mul_eq
  [CommRing K]
-- given
  (a : K)
  (n m : ℕ) :
-- imply
  a ^ (n * m) = (a ^ n) ^ m := by
-- proof
  apply AlgebraicCombinatorics.FPS.pow_mul_eq a n m

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma binomial_theorem
  [CommRing K]
-- given
  (a b : K)
  (n : ℕ) :
-- imply
  (a + b) ^ n = ∑ k ∈ Finset.range (n + 1), a ^ k * b ^ (n - k) * (n.choose k) := by
-- proof
  apply AlgebraicCombinatorics.FPS.binomial_theorem a b n

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma binomial_theorem_sub
  [CommRing K]
-- given
  (a b : K)
  (n : ℕ) :
-- imply
  (a - b) ^ n = ∑ m ∈ Finset.range (n + 1), (-1) ^ (m + n) * a ^ m * b ^ (n - m) * n.choose m := by
-- proof
  apply AlgebraicCombinatorics.FPS.binomial_theorem_sub a b n

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma module_add_comm
  [CommRing K]
  [AddCommGroup M]
  [Module K M]
-- given
  (a b : M) :
-- imply
  a + b = b + a := by
-- proof
  apply AlgebraicCombinatorics.FPS.module_add_comm a b

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma module_add_assoc
  [CommRing K]
  [AddCommGroup M]
  [Module K M]
-- given
  (a b c : M) :
-- imply
  a + (b + c) = (a + b) + c := by
-- proof
  apply AlgebraicCombinatorics.FPS.module_add_assoc a b c

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma module_add_zero
  [CommRing K]
  [AddCommGroup M]
  [Module K M]
-- given
  (a : M) :
-- imply
  a + 0 = a := by
-- proof
  apply AlgebraicCombinatorics.FPS.module_add_zero a

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma module_sub_iff_add
  [CommRing K]
  [AddCommGroup M]
  [Module K M]
-- given
  (a b c : M) :
-- imply
  a + b = c ↔ a = c - b := by
-- proof
  apply AlgebraicCombinatorics.FPS.module_sub_iff_add a b c

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma module_smul_assoc
  [CommRing K]
  [AddCommGroup M]
  [Module K M]
-- given
  (u v : K)
  (a : M) :
-- imply
  u • (v • a) = (u * v) • a := by
-- proof
  apply AlgebraicCombinatorics.FPS.module_smul_assoc u v a

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma module_smul_add
  [CommRing K]
  [AddCommGroup M]
  [Module K M]
-- given
  (u : K)
  (a b : M) :
-- imply
  u • (a + b) = u • a + u • b := by
-- proof
  apply AlgebraicCombinatorics.FPS.module_smul_add u a b

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma module_add_smul
  [CommRing K]
  [AddCommGroup M]
  [Module K M]
-- given
  (u v : K)
  (a : M) :
-- imply
  (u + v) • a = u • a + v • a := by
-- proof
  apply AlgebraicCombinatorics.FPS.module_add_smul u v a

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma module_one_smul
  [CommRing K]
  [AddCommGroup M]
  [Module K M]
-- given
  (a : M) :
-- imply
  (1 : K) • a = a := by
-- proof
  apply AlgebraicCombinatorics.FPS.module_one_smul a

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma module_zero_smul
  [CommRing K]
  [AddCommGroup M]
  [Module K M]
-- given
  (a : M) :
-- imply
  (0 : K) • a = 0 := by
-- proof
  apply AlgebraicCombinatorics.FPS.module_zero_smul a

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma module_smul_zero
  [CommRing K]
  [AddCommGroup M]
  [Module K M]
-- given
  (u : K) :
-- imply
  u • (0 : M) = 0 := by
-- proof
  apply AlgebraicCombinatorics.FPS.module_smul_zero u

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma module_neg_eq_neg_one_smul
  [CommRing K]
  [AddCommGroup M]
  [Module K M]
-- given
  (a : M) :
-- imply
  -a = (-1 : K) • a := by
-- proof
  apply AlgebraicCombinatorics.FPS.module_neg_eq_neg_one_smul a

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma module_sub_eq_add_neg
  [CommRing K]
  [AddCommGroup M]
  [Module K M]
-- given
  (a b : M) :
-- imply
  a - b = a + (-b) := by
-- proof
  apply AlgebraicCombinatorics.FPS.module_sub_eq_add_neg a b

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma module_sub_eq_add_neg_one_smul
  [CommRing K]
  [AddCommGroup M]
  [Module K M]
-- given
  (a b : M) :
-- imply
  a - b = a + (-1 : K) • b := by
-- proof
  apply AlgebraicCombinatorics.FPS.module_sub_eq_add_neg_one_smul a b

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma module_neg_add
  [CommRing K]
  [AddCommGroup M]
  [Module K M]
-- given
  (a b : M) :
-- imply
  -(a + b) = -a + -b := by
-- proof
  apply AlgebraicCombinatorics.FPS.module_neg_add a b

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma module_neg_neg
  [CommRing K]
  [AddCommGroup M]
  [Module K M]
-- given
  (a : M) :
-- imply
  -(-a) = a := by
-- proof
  apply AlgebraicCombinatorics.FPS.module_neg_neg a

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma sum_disjoint_union
  [CommRing K]
  [DecidableEq S]
-- given
  {X Y : Finset S}
  (hXY : Disjoint X Y)
  (f : S → K) :
-- imply
  ∑ s ∈ X ∪ Y, f s = ∑ s ∈ X, f s + ∑ s ∈ Y, f s := by
-- proof
  apply AlgebraicCombinatorics.FPS.sum_disjoint_union hXY f

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma sum_add_distrib'
  [CommRing K]
-- given
  {T : Finset S}
  (f g : S → K) :
-- imply
  ∑ s ∈ T, (f s + g s) = ∑ s ∈ T, f s + ∑ s ∈ T, g s := by
-- proof
  apply AlgebraicCombinatorics.FPS.sum_add_distrib' f g

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma sum_empty
  [CommRing K]
-- given
  (f : S → K) :
-- imply
  ∑ s ∈ (∅ : Finset S), f s = 0 := by
-- proof
  apply AlgebraicCombinatorics.FPS.sum_empty f

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma prod_empty
  [CommRing K]
-- given
  (f : S → K) :
-- imply
  ∏ s ∈ (∅ : Finset S), f s = 1 := by
-- proof
  apply AlgebraicCombinatorics.FPS.prod_empty f

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma isInverse_comm
  [CommRing L]
-- given
  (a b : L) :
-- imply
  IsInverse a b ↔ IsInverse b a := by
-- proof
  apply AlgebraicCombinatorics.FPS.isInverse_comm a b

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma isInverse_symm
  [CommRing L]
-- given
  {a b : L}
  (h : IsInverse a b) :
-- imply
  IsInverse b a := by
-- proof
  apply AlgebraicCombinatorics.FPS.isInverse_symm h

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma isInverse_one_one
  [CommRing L] :
-- imply
  IsInverse (1 : L) 1 := by
-- proof
  apply AlgebraicCombinatorics.FPS.isInverse_one_one

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma not_isInverse_zero_of_nontrivial
  [CommRing L]
  [Nontrivial L]
-- given
  (b : L) :
-- imply
  ¬IsInverse (0 : L) b := by
-- proof
  apply AlgebraicCombinatorics.FPS.not_isInverse_zero_of_nontrivial b

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma isInverse_unique
  [CommRing L]
-- given
  {a b c : L}
  (hab : IsInverse a b)
  (hac : IsInverse a c) :
-- imply
  b = c := by
-- proof
  apply AlgebraicCombinatorics.FPS.isInverse_unique hab hac

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma isInvertible_iff_isUnit
  [CommRing L]
-- given
  (a : L) :
-- imply
  IsInvertible a ↔ IsUnit a := by
-- proof
  apply AlgebraicCombinatorics.FPS.isInvertible_iff_isUnit a

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma isInvertible_one
  [CommRing L] :
-- imply
  IsInvertible (1 : L) := by
-- proof
  apply AlgebraicCombinatorics.FPS.isInvertible_one

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma not_isInvertible_zero
  [CommRing L]
  [Nontrivial L] :
-- imply
  ¬IsInvertible (0 : L) := by
-- proof
  apply AlgebraicCombinatorics.FPS.not_isInvertible_zero

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma isInvertible_mul
  [CommRing L]
-- given
  {a b : L}
  (ha : IsInvertible a)
  (hb : IsInvertible b) :
-- imply
  IsInvertible (a * b) := by
-- proof
  apply AlgebraicCombinatorics.FPS.isInvertible_mul ha hb

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma isInvertible_of_isInverse
  [CommRing L]
-- given
  {a b : L}
  (h : IsInverse a b) :
-- imply
  IsInvertible b := by
-- proof
  apply AlgebraicCombinatorics.FPS.isInvertible_of_isInverse h

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma int_isUnit_iff
-- given
  (n : ℤ) :
-- imply
  IsUnit n ↔ n = 1 ∨ n = -1 := by
-- proof
  apply AlgebraicCombinatorics.FPS.int_isUnit_iff n

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma field_isUnit_of_ne_zero
  [Field F]
-- given
  {a : F}
  (ha : a ≠ 0) :
-- imply
  IsUnit a := by
-- proof
  apply AlgebraicCombinatorics.FPS.field_isUnit_of_ne_zero ha

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma field_isUnit_iff
  [Field F]
-- given
  {a : F} :
-- imply
  IsUnit a ↔ a ≠ 0 := by
-- proof
  apply AlgebraicCombinatorics.FPS.field_isUnit_iff

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma units_isInverse
  [CommRing L]
-- given
  (u : Lˣ) :
-- imply
  IsInverse (u : L) (u⁻¹ : Lˣ) := by
-- proof
  apply AlgebraicCombinatorics.FPS.units_isInverse u

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma units_isInvertible
  [CommRing L]
-- given
  (u : Lˣ) :
-- imply
  IsInvertible (u : L) := by
-- proof
  apply AlgebraicCombinatorics.FPS.units_isInvertible u

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma unitOfInverse_val
  [CommRing L]
-- given
  {a b : L}
  (h : IsInverse a b) :
-- imply
  (unitOfInverse h : L) = a := by
-- proof
  apply AlgebraicCombinatorics.FPS.unitOfInverse_val h

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma unit_mul_inv
  [CommRing L]
-- given
  (u : Lˣ) :
-- imply
  (u : L) * (u⁻¹ : Lˣ) = 1 := by
-- proof
  apply AlgebraicCombinatorics.FPS.unit_mul_inv u

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma unit_inv_mul
  [CommRing L]
-- given
  (u : Lˣ) :
-- imply
  (u⁻¹ : Lˣ) * (u : L) = 1 := by
-- proof
  apply AlgebraicCombinatorics.FPS.unit_inv_mul u

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma inverse_unique'
  [CommRing L]
-- given
  {a b c : L}
  (hb : a * b = 1)
  (hc : a * c = 1) :
-- imply
  b = c := by
-- proof
  apply AlgebraicCombinatorics.FPS.inverse_unique' hb hc

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma fraction_eq_divByUnit
  [CommRing L]
-- given
  (b : L)
  (u : Lˣ) :
-- imply
  fraction b u = AlgebraicCombinatorics.divByUnit b u := by
-- proof
  apply AlgebraicCombinatorics.FPS.fraction_eq_divByUnit b u

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma fraction_eq_iff
  [CommRing L]
-- given
  (b c : L)
  (u : Lˣ) :
-- imply
  fraction b u = c ↔ b = c * u := by
-- proof
  apply AlgebraicCombinatorics.FPS.fraction_eq_iff b c u

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma fraction_one
  [CommRing L]
-- given
  (u : Lˣ) :
-- imply
  fraction 1 u = (u⁻¹ : Lˣ) := by
-- proof
  apply AlgebraicCombinatorics.FPS.fraction_one u

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma fraction_unit_one
  [CommRing L]
-- given
  (b : L) :
-- imply
  fraction b 1 = b := by
-- proof
  apply AlgebraicCombinatorics.FPS.fraction_unit_one b

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma unit_zpow_neg
  [CommRing L]
-- given
  (u : Lˣ)
  (n : ℕ) :
-- imply
  u ^ (-(n : ℤ)) = (u⁻¹ : Lˣ) ^ n := by
-- proof
  apply AlgebraicCombinatorics.FPS.unit_zpow_neg u n

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma unit_zpow_neg_one
  [CommRing L]
-- given
  (u : Lˣ) :
-- imply
  u ^ (-1 : ℤ) = u⁻¹ := by
-- proof
  apply AlgebraicCombinatorics.FPS.unit_zpow_neg_one u

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma unit_zpow_add
  [CommRing L]
-- given
  (u : Lˣ)
  (m n : ℤ) :
-- imply
  u ^ (m + n) = u ^ m * u ^ n := by
-- proof
  apply AlgebraicCombinatorics.FPS.unit_zpow_add u m n

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma unit_zpow_mul
  [CommRing L]
-- given
  (u : Lˣ)
  (m n : ℤ) :
-- imply
  (u ^ m) ^ n = u ^ (m * n) := by
-- proof
  apply AlgebraicCombinatorics.FPS.unit_zpow_mul u m n

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma unit_inv_zpow
  [CommRing L]
-- given
  (u : Lˣ)
  (n : ℤ) :
-- imply
  (u ^ n)⁻¹ = u ^ (-n) := by
-- proof
  apply AlgebraicCombinatorics.FPS.unit_inv_zpow u n


-- created on 2026-10-20
