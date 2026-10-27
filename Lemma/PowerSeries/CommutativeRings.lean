import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.RingTheory.PowerSeries.CommutativeRings.Part3
import Lemma.PowerSeries.DividingFPS
open AlgebraicCombinatorics.FPS
open scoped BigOperators


section
-- ac-theorems


namespace AlgebraicCombinatorics.FPS


section CommRingBasics

variable {K : Type*} [CommRing K]

/-- **Commutativity of addition** (Axiom 1 in def.alg.commring):
    `a + b = b + a` for all `a, b ∈ K`. -/
lemma commRing_add_comm (a b : K) : a + b = b + a := add_comm a b

/-- **Associativity of addition** (Axiom 2 in def.alg.commring):
    `a + (b + c) = (a + b) + c` for all `a, b, c ∈ K`. -/
lemma commRing_add_assoc (a b c : K) : a + (b + c) = (a + b) + c := (add_assoc a b c).symm

/-- **Neutrality of zero** (Axiom 3 in def.alg.commring):
    `a + 0 = a` for all `a ∈ K`. -/
lemma commRing_add_zero (a : K) : a + 0 = a := add_zero a

/-- **Neutrality of zero** (Axiom 3 in def.alg.commring):
    `0 + a = a` for all `a ∈ K`. -/
lemma commRing_zero_add (a : K) : 0 + a = a := zero_add a

/-- **Subtraction undoes addition** (Axiom 4 in def.alg.commring):
    `a + b = c ↔ a = c - b` for all `a, b, c ∈ K`. -/
lemma commRing_sub_iff_add (a b c : K) : a + b = c ↔ a = c - b := by
  constructor
  · intro h; rw [← h, add_sub_cancel_right]
  · intro h; rw [h, sub_add_cancel]

/-- **Commutativity of multiplication** (Axiom 5 in def.alg.commring):
    `a * b = b * a` for all `a, b ∈ K`. -/
lemma commRing_mul_comm (a b : K) : a * b = b * a := mul_comm a b

/-- **Associativity of multiplication** (Axiom 6 in def.alg.commring):
    `a * (b * c) = (a * b) * c` for all `a, b, c ∈ K`. -/
lemma commRing_mul_assoc (a b c : K) : a * (b * c) = (a * b) * c := (mul_assoc a b c).symm

/-- **Distributivity** (Axiom 7 in def.alg.commring):
    `a * (b + c) = a * b + a * c` for all `a, b, c ∈ K`. -/
lemma commRing_left_distrib (a b c : K) : a * (b + c) = a * b + a * c := mul_add a b c

/-- **Distributivity** (Axiom 7 in def.alg.commring):
    `(a + b) * c = a * c + b * c` for all `a, b, c ∈ K`. -/
lemma commRing_right_distrib (a b c : K) : (a + b) * c = a * c + b * c := add_mul a b c

/-- **Neutrality of one** (Axiom 8 in def.alg.commring):
    `a * 1 = a` for all `a ∈ K`. -/
lemma commRing_mul_one (a : K) : a * 1 = a := mul_one a

/-- **Neutrality of one** (Axiom 8 in def.alg.commring):
    `1 * a = a` for all `a ∈ K`. -/
lemma commRing_one_mul (a : K) : 1 * a = a := one_mul a

/-- **Annihilation** (Axiom 9 in def.alg.commring):
    `a * 0 = 0` for all `a ∈ K`. -/
lemma commRing_mul_zero (a : K) : a * 0 = 0 := mul_zero a

/-- **Annihilation** (Axiom 9 in def.alg.commring):
    `0 * a = 0` for all `a ∈ K`. -/
lemma commRing_zero_mul (a : K) : 0 * a = 0 := zero_mul a

end CommRingBasics


section CommRingExamples

end CommRingExamples


section StandardRules

variable {K : Type*} [CommRing K]

/-- Negation distributes over addition: `-(a + b) = (-a) + (-b)`. -/
lemma neg_add_distrib (a b : K) : -(a + b) = -a + -b := neg_add a b

/-- Double negation: `-(-a) = a`. -/
lemma neg_neg_eq (a : K) : -(-a) = a := neg_neg a

/-- Scalar multiplication by integers distributes: `(n + m) • a = n • a + m • a`. -/
lemma add_zsmul_distrib (a : K) (n m : ℤ) : (n + m) • a = n • a + m • a := by rw [add_smul]

/-- Scalar multiplication by integers is associative: `(n * m) • a = n • (m • a)`. -/
lemma mul_zsmul_assoc (a : K) (n m : ℤ) : (n * m) • a = n • (m • a) := by rw [mul_smul]

/-- Multiplication distributes over subtraction: `a * (b - c) = a * b - a * c`. -/
lemma mul_sub_distrib (a b c : K) : a * (b - c) = a * b - a * c := mul_sub a b c

/-- Power of a product: `(a * b)^n = a^n * b^n`. -/
lemma mul_pow_eq (a b : K) (n : ℕ) : (a * b) ^ n = a ^ n * b ^ n := mul_pow a b n

/-- Power addition rule: `a^(n+m) = a^n * a^m`. -/
lemma pow_add_eq (a : K) (n m : ℕ) : a ^ (n + m) = a ^ n * a ^ m := pow_add a n m

/-- Power multiplication rule: `a^(n*m) = (a^n)^m`. -/
lemma pow_mul_eq (a : K) (n m : ℕ) : a ^ (n * m) = (a ^ n) ^ m := pow_mul a n m

/-- **The Binomial Theorem** (mentioned in def.alg.commring):
    `(a + b)^n = ∑_{k=0}^n C(n,k) * a^k * b^(n-k)`.

    In Mathlib, this is `add_pow` from `Mathlib.Data.Nat.Choose.Sum`. -/
lemma binomial_theorem (a b : K) (n : ℕ) :
    (a + b) ^ n = ∑ k ∈ Finset.range (n + 1), a ^ k * b ^ (n - k) * (n.choose k) :=
  add_pow a b n

/-- Variant of the binomial theorem with subtraction. -/
lemma binomial_theorem_sub (a b : K) (n : ℕ) :
    (a - b) ^ n = ∑ m ∈ Finset.range (n + 1), (-1) ^ (m + n) * a ^ m * b ^ (n - m) * n.choose m :=
  sub_pow a b n

end StandardRules


section ModuleBasics

variable {K : Type*} [CommRing K]
variable {M : Type*} [AddCommGroup M] [Module K M]

/-- **Commutativity of addition** (Axiom 1 in def.alg.module):
    `a + b = b + a` for all `a, b ∈ M`. -/
lemma module_add_comm (a b : M) : a + b = b + a := add_comm a b

/-- **Associativity of addition** (Axiom 2 in def.alg.module):
    `a + (b + c) = (a + b) + c` for all `a, b, c ∈ M`. -/
lemma module_add_assoc (a b c : M) : a + (b + c) = (a + b) + c := (add_assoc a b c).symm

/-- **Neutrality of zero** (Axiom 3 in def.alg.module):
    `a + 0 = a` for all `a ∈ M`. -/
lemma module_add_zero (a : M) : a + 0 = a := add_zero a

/-- **Subtraction undoes addition** (Axiom 4 in def.alg.module):
    `a + b = c ↔ a = c - b` for all `a, b, c ∈ M`. -/
lemma module_sub_iff_add (a b c : M) : a + b = c ↔ a = c - b := by
  constructor
  · intro h; rw [← h, add_sub_cancel_right]
  · intro h; rw [h, sub_add_cancel]

/-- **Associativity of scaling** (Axiom 5 in def.alg.module):
    `u • (v • a) = (u * v) • a` for all `u, v ∈ K` and `a ∈ M`. -/
lemma module_smul_assoc (u v : K) (a : M) : u • (v • a) = (u * v) • a := by
  rw [mul_smul]

/-- **Left distributivity** (Axiom 6 in def.alg.module):
    `u • (a + b) = u • a + u • b` for all `u ∈ K` and `a, b ∈ M`. -/
lemma module_smul_add (u : K) (a b : M) : u • (a + b) = u • a + u • b := smul_add u a b

/-- **Right distributivity** (Axiom 7 in def.alg.module):
    `(u + v) • a = u • a + v • a` for all `u, v ∈ K` and `a ∈ M`. -/
lemma module_add_smul (u v : K) (a : M) : (u + v) • a = u • a + v • a := add_smul u v a

/-- **Neutrality of one** (Axiom 8 in def.alg.module):
    `1 • a = a` for all `a ∈ M`. -/
lemma module_one_smul (a : M) : (1 : K) • a = a := one_smul K a

/-- **Left annihilation** (Axiom 9 in def.alg.module):
    `0 • a = 0` for all `a ∈ M`. -/
lemma module_zero_smul (a : M) : (0 : K) • a = 0 := zero_smul K a

/-- **Right annihilation** (Axiom 10 in def.alg.module):
    `u • 0 = 0` for all `u ∈ K`. -/
lemma module_smul_zero (u : K) : u • (0 : M) = 0 := smul_zero u


/-- **Additive inverse via scaling** (Note in def.alg.module):
    The additive inverse of `a` can be constructed as `(-1) • a`.
    This shows why modules don't need explicit negation in their axioms. -/
lemma module_neg_eq_neg_one_smul (a : M) : -a = (-1 : K) • a := by
  rw [neg_one_smul]

/-- Subtraction can be expressed as addition of the negation. -/
lemma module_sub_eq_add_neg (a b : M) : a - b = a + (-b) := sub_eq_add_neg a b

/-- Subtraction can be expressed using scaling by `-1`. -/
lemma module_sub_eq_add_neg_one_smul (a b : M) : a - b = a + (-1 : K) • b := by
  rw [neg_one_smul, sub_eq_add_neg]

/-- Negation distributes over addition in a module. -/
lemma module_neg_add (a b : M) : -(a + b) = -a + -b := neg_add a b

/-- Double negation in a module. -/
lemma module_neg_neg (a : M) : -(-a) = a := neg_neg a

end ModuleBasics


section ModuleExamples

end ModuleExamples


section FiniteSumsProducts

variable {K : Type*} [CommRing K]
variable {S : Type*}


/-- Empty sum equals zero. -/
lemma sum_empty (f : S → K) : ∑ _s ∈ (∅ : Finset S), f _s = 0 :=
  Finset.sum_empty

/-- Empty product equals one. -/
lemma prod_empty (f : S → K) : ∏ _s ∈ (∅ : Finset S), f _s = 1 :=
  Finset.prod_empty
/-- Finite sums can be split over disjoint sets. -/
lemma sum_disjoint_union [DecidableEq S] {X Y : Finset S} (hXY : Disjoint X Y) (f : S → K) :
    ∑ s ∈ X ∪ Y, f s = ∑ s ∈ X, f s + ∑ s ∈ Y, f s :=
  Finset.sum_union hXY

/-- Finite sums distribute over addition. -/
lemma sum_add_distrib' {T : Finset S} (f g : S → K) :
    ∑ s ∈ T, (f s + g s) = ∑ s ∈ T, f s + ∑ s ∈ T, g s :=
  Finset.sum_add_distrib

end FiniteSumsProducts


section InverseDefinition

variable {L : Type*} [CommRing L]

/-- In a commutative ring, `IsInverse a b` is symmetric: if `a * b = 1`, then `b * a = 1`. -/
lemma isInverse_comm (a b : L) : IsInverse a b ↔ IsInverse b a := by
  simp only [IsInverse, mul_comm]

/-- The inverse relation is symmetric in commutative rings. -/
lemma isInverse_symm {a b : L} (h : IsInverse a b) : IsInverse b a := by
  rwa [isInverse_comm]

/-- `1` is an inverse of `1`. -/
lemma isInverse_one_one : IsInverse (1 : L) 1 := by simp [IsInverse]

/-- `0` has no inverse (unless `L` is the trivial ring where `0 = 1`). -/
lemma not_isInverse_zero_of_nontrivial [Nontrivial L] (b : L) : ¬IsInverse (0 : L) b := by
  simp [IsInverse]

/-- If `a` has an inverse, then `a * b = 1` implies `b` is that inverse.
    Label: thm.commring.inverse-uni -/
lemma isInverse_unique {a b c : L} (hab : IsInverse a b) (hac : IsInverse a c) : b = c := by
  have hab' : a * b = 1 := hab
  have hac' : a * c = 1 := hac
  have hba : b * a = 1 := isInverse_symm hab
  calc b = b * 1 := (mul_one b).symm
       _ = b * (a * c) := by rw [hac']
       _ = (b * a) * c := by ring
       _ = 1 * c := by rw [hba]
       _ = c := one_mul c

/-- `1` is invertible. -/
lemma isInvertible_one : IsInvertible (1 : L) := ⟨1, isInverse_one_one⟩

/-- `0` is not invertible in a nontrivial ring. -/
lemma not_isInvertible_zero [Nontrivial L] : ¬IsInvertible (0 : L) := by
  intro ⟨b, hb⟩
  exact not_isInverse_zero_of_nontrivial b hb

/-- The product of two invertible elements is invertible. -/
lemma isInvertible_mul {a b : L} (ha : IsInvertible a) (hb : IsInvertible b) :
    IsInvertible (a * b) := by
  rw [isInvertible_iff_isUnit] at *
  exact ha.mul hb

/-- The inverse of an invertible element is invertible. -/
lemma isInvertible_of_isInverse {a b : L} (h : IsInverse a b) : IsInvertible b :=
  ⟨a, isInverse_symm h⟩


/-- In `ℤ`, the only units are `1` and `-1`. -/
lemma int_isUnit_iff (n : ℤ) : IsUnit n ↔ n = 1 ∨ n = -1 := Int.isUnit_iff

/-- In a field, every nonzero element is invertible. -/
lemma field_isUnit_of_ne_zero {F : Type*} [Field F] {a : F} (ha : a ≠ 0) : IsUnit a :=
  IsUnit.mk0 a ha

/-- In a field, `a` is invertible iff `a ≠ 0`. -/
lemma field_isUnit_iff {F : Type*} [Field F] {a : F} : IsUnit a ↔ a ≠ 0 := by
  constructor
  · intro ha h
    simp [h] at ha
  · exact field_isUnit_of_ne_zero


/-- Every unit satisfies the inverse property: `u * u⁻¹ = 1`. -/
lemma units_isInverse (u : Lˣ) : IsInverse (u : L) (u⁻¹ : Lˣ) := Units.mul_inv u

/-- The coercion from `Lˣ` to `L` gives an invertible element. -/
lemma units_isInvertible (u : Lˣ) : IsInvertible (u : L) :=
  ⟨(u⁻¹ : Lˣ), units_isInverse u⟩

/-- The constructed unit has the expected value. -/
lemma unitOfInverse_val {a b : L} (h : IsInverse a b) : (unitOfInverse h : L) = a := by
  simp [unitOfInverse]

end InverseDefinition


section InversesAndFractions

variable {L : Type*} [CommRing L]


/-- For a unit `u`, the inverse satisfies `u * u⁻¹ = 1`.
    Label: def.commring.fracs (a) -/
lemma unit_mul_inv (u : Lˣ) : (u : L) * (u⁻¹ : Lˣ) = 1 := Units.mul_inv u

/-- For a unit `u`, the inverse satisfies `u⁻¹ * u = 1`.
    Label: def.commring.fracs (a) -/
lemma unit_inv_mul (u : Lˣ) : (u⁻¹ : Lˣ) * (u : L) = 1 := Units.inv_mul u

/-- The inverse of a unit is unique: if `a * b = 1` and `a * c = 1`, then `b = c`.
    This is `thm.commring.inverse-uni` from the source.
    Label: def.commring.fracs (a) -/
lemma inverse_unique' {a b c : L} (hb : a * b = 1) (hc : a * c = 1) : b = c := by
  have h1 : b = b * 1 := (mul_one b).symm
  have h2 : b * 1 = b * (a * c) := by rw [hc]
  have h3 : b * (a * c) = (b * a) * c := (mul_assoc b a c).symm
  have h4 : (b * a) * c = (a * b) * c := by rw [mul_comm b a]
  have h5 : (a * b) * c = 1 * c := by rw [hb]
  have h6 : 1 * c = c := one_mul c
  calc b = b * 1 := h1
       _ = b * (a * c) := h2
       _ = (b * a) * c := h3
       _ = (a * b) * c := h4
       _ = 1 * c := h5
       _ = c := h6

/-- Bridge lemma: `fraction` is definitionally equal to `divByUnit`.
    This connects the pedagogical definition in this file to the one in `DividingFPS.lean`. -/
lemma fraction_eq_divByUnit (b : L) (u : Lˣ) :
    fraction b u = AlgebraicCombinatorics.divByUnit b u := rfl

/-- Alternative characterization: `b/a = c` iff `b = c * a`.
    Label: def.commring.fracs (b) -/
lemma fraction_eq_iff (b c : L) (u : Lˣ) : fraction b u = c ↔ b = c * u := by
  simp only [fraction]
  constructor
  · intro h
    calc b = b * 1 := (mul_one b).symm
         _ = b * ((u⁻¹ : Lˣ) * u) := by rw [Units.inv_mul]
         _ = (b * (u⁻¹ : Lˣ)) * u := (mul_assoc b (u⁻¹ : Lˣ) u).symm
         _ = c * u := by rw [h]
  · intro h
    calc b * (u⁻¹ : Lˣ) = (c * u) * (u⁻¹ : Lˣ) := by rw [h]
         _ = c * (u * (u⁻¹ : Lˣ)) := mul_assoc c u (u⁻¹ : Lˣ)
         _ = c * 1 := by rw [Units.mul_inv]
         _ = c := mul_one c

/-- Fraction of 1 equals the inverse: `1/a = a⁻¹`.
    Label: def.commring.fracs (b) -/
lemma fraction_one (u : Lˣ) : fraction 1 u = (u⁻¹ : Lˣ) := one_mul _

/-- Fraction with identity denominator: `b/1 = b`.
    Label: def.commring.fracs (b) -/
lemma fraction_unit_one (b : L) : fraction b 1 = b := by
  simp [fraction]


/-- For a unit, `u^(-n) = (u⁻¹)^n` for any natural number `n`.
    This is the definition of negative powers.
    Label: def.commring.fracs (c) -/
lemma unit_zpow_neg (u : Lˣ) (n : ℕ) : u ^ (-(n : ℤ)) = (u⁻¹ : Lˣ) ^ n := by
  simp [zpow_neg, zpow_natCast]

/-- For a unit, `u^(-1) = u⁻¹`.
    Label: def.commring.fracs (c) -/
lemma unit_zpow_neg_one (u : Lˣ) : u ^ (-1 : ℤ) = u⁻¹ := zpow_neg_one u

/-- Power addition rule extends to integer exponents: `u^(m+n) = u^m * u^n`.
    Label: def.commring.fracs (c) -/
lemma unit_zpow_add (u : Lˣ) (m n : ℤ) : u ^ (m + n) = u ^ m * u ^ n := zpow_add u m n

/-- Power of power rule for integer exponents: `(u^m)^n = u^(m*n)`.
    Label: def.commring.fracs (c) -/
lemma unit_zpow_mul (u : Lˣ) (m n : ℤ) : (u ^ m) ^ n = u ^ (m * n) := (zpow_mul u m n).symm

/-- Inverse of a power: `(u^n)⁻¹ = u^(-n)`.
    Label: def.commring.fracs (c) -/
lemma unit_inv_zpow (u : Lˣ) (n : ℤ) : (u ^ n)⁻¹ = u ^ (-n) := by
  rw [← zpow_neg_one, ← zpow_mul]
  ring_nf

end InversesAndFractions

end AlgebraicCombinatorics.FPS
end


/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma pv_commRing_add_comm
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
private lemma pv_commRing_add_assoc
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
private lemma pv_commRing_add_zero
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
private lemma pv_commRing_zero_add
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
private lemma pv_commRing_sub_iff_add
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
private lemma pv_commRing_mul_comm
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
private lemma pv_commRing_mul_assoc
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
private lemma pv_commRing_left_distrib
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
private lemma pv_commRing_right_distrib
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
private lemma pv_commRing_mul_one
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
private lemma pv_commRing_one_mul
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
private lemma pv_commRing_mul_zero
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
private lemma pv_commRing_zero_mul
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
private lemma pv_neg_add_distrib
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
private lemma pv_neg_neg_eq
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
private lemma pv_add_zsmul_distrib
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
private lemma pv_mul_zsmul_assoc
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
private lemma pv_mul_sub_distrib
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
private lemma pv_mul_pow_eq
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
private lemma pv_pow_add_eq
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
private lemma pv_pow_mul_eq
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
private lemma pv_binomial_theorem
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
private lemma pv_binomial_theorem_sub
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
private lemma pv_module_add_comm
  [AddCommGroup M]
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
private lemma pv_module_add_assoc
  [AddCommGroup M]
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
private lemma pv_module_add_zero
  [AddCommGroup M]
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
private lemma pv_module_sub_iff_add
  [AddCommGroup M]
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
private lemma pv_module_smul_assoc
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
private lemma pv_module_smul_add
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
private lemma pv_module_add_smul
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
private lemma pv_module_one_smul
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
private lemma pv_module_zero_smul
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
private lemma pv_module_smul_zero
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
private lemma pv_module_neg_eq_neg_one_smul
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
private lemma pv_module_sub_eq_add_neg
  [AddCommGroup M]
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
private lemma pv_module_sub_eq_add_neg_one_smul
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
private lemma pv_module_neg_add
  [AddCommGroup M]
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
private lemma pv_module_neg_neg
  [AddCommGroup M]
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
private lemma pv_sum_disjoint_union
  [CommRing K]
  [DecidableEq S]
  {X Y : Finset S}
-- given
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
private lemma pv_sum_add_distrib'
  [CommRing K]
  {T : Finset S}
-- given
  (f g : S → K) :
-- imply
  ∑ s ∈ T, (f s + g s) = ∑ s ∈ T, f s + ∑ s ∈ T, g s := by
-- proof
  apply AlgebraicCombinatorics.FPS.sum_add_distrib' f g

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma pv_sum_empty
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
private lemma pv_prod_empty
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
private lemma pv_isInverse_comm
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
private lemma pv_isInverse_symm
  [CommRing L]
  {a b : L}
-- given
  (h : IsInverse a b) :
-- imply
  IsInverse b a := by
-- proof
  apply AlgebraicCombinatorics.FPS.isInverse_symm h

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma pv_isInverse_one_one
  [CommRing L] :
-- imply
  IsInverse (1 : L) 1 := by
-- proof
  apply AlgebraicCombinatorics.FPS.isInverse_one_one

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma pv_not_isInverse_zero_of_nontrivial
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
private lemma pv_isInverse_unique
  [CommRing L]
  {a b c : L}
-- given
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
private lemma pv_isInvertible_one
  [CommRing L] :
-- imply
  IsInvertible (1 : L) := by
-- proof
  apply AlgebraicCombinatorics.FPS.isInvertible_one

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma pv_not_isInvertible_zero
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
private lemma pv_isInvertible_mul
  [CommRing L]
  {a b : L}
-- given
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
private lemma pv_isInvertible_of_isInverse
  [CommRing L]
  {a b : L}
-- given
  (h : IsInverse a b) :
-- imply
  IsInvertible b := by
-- proof
  apply AlgebraicCombinatorics.FPS.isInvertible_of_isInverse h

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma pv_int_isUnit_iff
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
private lemma pv_field_isUnit_of_ne_zero
  [Field F]
  {a : F}
-- given
  (ha : a ≠ 0) :
-- imply
  IsUnit a := by
-- proof
  apply AlgebraicCombinatorics.FPS.field_isUnit_of_ne_zero ha

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma pv_field_isUnit_iff
  [Field F]
  {a : F} :
-- imply
  IsUnit a ↔ a ≠ 0 := by
-- proof
  apply AlgebraicCombinatorics.FPS.field_isUnit_iff

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma pv_units_isInverse
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
private lemma pv_units_isInvertible
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
private lemma pv_unitOfInverse_val
  [CommRing L]
  {a b : L}
-- given
  (h : IsInverse a b) :
-- imply
  (unitOfInverse h : L) = a := by
-- proof
  apply AlgebraicCombinatorics.FPS.unitOfInverse_val h

/--
[CommutativeRings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/CommutativeRings.lean)
-/
@[path]
private lemma pv_unit_mul_inv
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
private lemma pv_unit_inv_mul
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
private lemma pv_inverse_unique'
  [CommRing L]
  {a b c : L}
-- given
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
private lemma pv_fraction_eq_divByUnit
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
private lemma pv_fraction_eq_iff
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
private lemma pv_fraction_one
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
private lemma pv_fraction_unit_one
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
private lemma pv_unit_zpow_neg
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
private lemma pv_unit_zpow_neg_one
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
private lemma pv_unit_zpow_add
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
private lemma pv_unit_zpow_mul
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
private lemma pv_unit_inv_zpow
  [CommRing L]
-- given
  (u : Lˣ)
  (n : ℤ) :
-- imply
  (u ^ n)⁻¹ = u ^ (-n) := by
-- proof
  apply AlgebraicCombinatorics.FPS.unit_inv_zpow u n


-- created on 2026-10-20
-- updated on 2026-10-26
