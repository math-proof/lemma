import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.RingTheory.HahnSeries.LaurentSeries.Part6
import Lemma.LaurentSeries.LaurentSeries
open AlgebraicCombinatorics.FPS.Laurent
open LaurentPolynomial
open HahnSeries
open scoped LaurentPolynomial Polynomial BigOperators


section
-- ac-theorems


open scoped LaurentPolynomial Polynomial
open LaurentPolynomial HahnSeries

-- `AddMonoidAlgebra` is a wrapper around `M →₀ R` (`coeff`), not the `Finsupp` itself.
namespace AddMonoidAlgebra


end AddMonoidAlgebra

noncomputable section

namespace AlgebraicCombinatorics.FPS.Laurent


section LaurentPolynomialDefinition

variable {K : Type*} [CommRing K]

/-- Laurent polynomials are essentially finite families: they have finite support. -/
lemma laurentPoly_finite_support (p : LaurentPoly K) : (p.support : Set ℤ).Finite :=
  p.support.finite_toSet

/-- **Multiplication of Laurent polynomials is convolution**.
(Part of Definition def.fps.laure.laupol)

The product (a · b)_n = ∑_{i∈ℤ} aᵢ · b_{n-i}.

In Mathlib, this is the standard multiplication on `AddMonoidAlgebra K ℤ`. -/
lemma laurentPoly_mul_coeff (a b : LaurentPoly K) (n : ℤ) :
    (a * b) n = ∑ i ∈ a.support, a i * b (n - i) := by
  simp only [AddMonoidAlgebra.mul_apply, Finsupp.sum]
  apply Finset.sum_congr rfl
  intro i _
  have key : ∀ x, (if i + x = n then a i * b x else 0) =
             (if x = n - i then a i * b x else 0) := fun x => by
    by_cases h : i + x = n
    · have hx : x = n - i := by linarith
      simp [hx]
    · have hx : ¬(x = n - i) := fun hx => h (by linarith)
      simp [h, hx]
  simp_rw [key]
  rw [Finset.sum_ite_eq']
  by_cases h : n - i ∈ b.support
  · have hmem : n - i ∈ b.coeff.support := by
      simpa [AddMonoidAlgebra.support] using h
    rw [if_pos hmem]
  · simp only [AddMonoidAlgebra.support, Finsupp.mem_support_iff, not_not] at h
    simp [h]

/-- The indeterminate x has coefficient 1 at position 1 and 0 elsewhere. -/
@[simp]
lemma laurentPoly_X_coeff (n : ℤ) :
    (laurentPoly_X (K := K)) n = if n = 1 then 1 else 0 := by
  simp only [laurentPoly_X]
  rw [T_apply]
  by_cases h : n = 1
  · simp [h]
  · simp [h, Ne.symm h]

/-- **The unity element in Laurent polynomials**.
(Part of Theorem thm.fps.laure.laupol-ring)

The unity is 1 = (δ_{i,0})_{i∈ℤ}, i.e., the sequence with 1 at position 0 and 0 elsewhere. -/
@[simp]
lemma laurentPoly_one_coeff (n : ℤ) :
    (1 : LaurentPoly K) n = if n = 0 then 1 else 0 := by
  rw [← T_zero]
  change (T (0 : ℤ) : K[T;T⁻¹]).coeff n = _
  rw [T_apply]
  simp [eq_comm]

/-- The unity element equals T(0). -/
lemma laurentPoly_one_eq_T_zero : (1 : LaurentPoly K) = T 0 := rfl

/-- Scalar multiplication on Laurent polynomials acts coefficientwise.
(Part of Definition def.fps.laure.laupol) -/
lemma laurentPoly_smul_coeff (c : K) (p : LaurentPoly K) (n : ℤ) :
    (c • p) n = c * p n := rfl

/-- Addition on Laurent polynomials is coefficientwise.
(Part of Definition def.fps.laure.laupol) -/
lemma laurentPoly_add_coeff (p q : LaurentPoly K) (n : ℤ) :
    (p + q) n = p n + q n := by
  simpa using Finsupp.add_apply p.coeff q.coeff n

/-- The zero Laurent polynomial has all coefficients zero. -/
lemma laurentPoly_zero_coeff (n : ℤ) : (0 : LaurentPoly K) n = 0 := by
  simpa using Finsupp.zero_apply (α := ℤ) (M := K) n

/-- **The support of a Laurent polynomial is finite**.
(Key property from Definition def.fps.laure.laupol)

This is the essential finiteness condition: only finitely many coefficients are nonzero. -/
lemma laurentPoly_support_finite (p : LaurentPoly K) :
    {n : ℤ | p n ≠ 0}.Finite := by
  have h : {n : ℤ | p n ≠ 0} = (p.support : Set ℤ) := by
    ext n
    simp [AddMonoidAlgebra.support, Finsupp.mem_support_iff]
  simpa [h] using p.support.finite_toSet

/-- The support of a Laurent polynomial is exactly the Finsupp support. -/
lemma laurentPoly_support_eq (p : LaurentPoly K) :
    {n : ℤ | p n ≠ 0} = ↑p.support := by
  ext n
  simp [AddMonoidAlgebra.support, Finsupp.mem_support_iff]

/-- The coefficients of a Laurent polynomial constructed from a finsupp are the same. -/
lemma laurentPoly_ofFinsupp_coeff (f : ℤ →₀ K) (n : ℤ) :
    laurentPoly_ofFinsupp f n = f n := rfl

/-- The coefficient of a single-term Laurent polynomial. -/
lemma laurentPoly_single_coeff (k : ℤ) (a : K) (n : ℤ) :
    laurentPoly_single k a n = if n = k then a else 0 := by
  simp only [laurentPoly_single, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  split_ifs with h1 h2
  · rfl
  · omega
  · omega
  · rfl

/-- A single-term Laurent polynomial equals C(a) * T(k). -/
lemma laurentPoly_single_eq_C_mul_T (k : ℤ) (a : K) :
    laurentPoly_single k a = C a * T k := by
  simp only [laurentPoly_single, single_eq_C_mul_T]

/-- **Laurent polynomials are the essentially finite families**.

This theorem explicitly states that Laurent polynomials (as `ℤ →₀ K`) are exactly
the essentially finite families (aₙ)_{n∈ℤ}, formalizing Definition def.fps.laure.laupol. -/
lemma laurentPoly_iff_essentiallyFinite (f : ℤ → K) :
    (∃ p : LaurentPoly K, ∀ n, p n = f n) ↔ {n : ℤ | f n ≠ 0}.Finite := by
  constructor
  · intro ⟨p, hp⟩
    have h := laurentPoly_support_finite p
    have heq : {n : ℤ | f n ≠ 0} = {n : ℤ | p n ≠ 0} := by
      ext n
      simp only [Set.mem_ofPred_eq]
      change f n ≠ 0 ↔ p.coeff n ≠ 0
      rw [← hp n]
    rw [heq]
    exact h
  · intro hf
    refine ⟨⟨hf.toFinset, fun n => f n, ?_⟩, fun n => rfl⟩
    intro n
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, ne_eq]

end LaurentPolynomialDefinition

section LaurentPolynomialBasics

variable {K : Type*} [CommRing K]

/-- The variable `T` in Laurent polynomials is a unit (invertible).
(Part of Theorem thm.fps.laure.laupol-ring) -/
lemma T_isUnit : IsUnit (T 1 : K[T;T⁻¹]) := by
  refine ⟨⟨T 1, T (-1), ?_, ?_⟩, rfl⟩
  · have h := T_add (R := K) 1 (-1)
    simp only [add_neg_cancel] at h
    exact h.symm
  · have h := T_add (R := K) (-1) 1
    simp only [neg_add_cancel] at h
    exact h.symm

/-- The inverse of `T` is `T⁻¹ = T(-1)`.
(Part of Theorem thm.fps.laure.laupol-ring) -/
lemma T_inv : (T 1 : K[T;T⁻¹]) * T (-1) = 1 := by
  have h := T_add (R := K) 1 (-1)
  simp only [add_neg_cancel] at h
  exact h.symm

/-- `T(-1) * T = 1`.
(Part of Theorem thm.fps.laure.laupol-ring) -/
lemma T_neg_one_mul_T : (T (-1) : K[T;T⁻¹]) * T 1 = 1 := by
  have h := T_add (R := K) (-1) 1
  simp only [neg_add_cancel] at h
  exact h.symm

end LaurentPolynomialBasics


section ShiftByT

variable {K : Type*} [CommRing K]

/-- **Multiplication by T shifts coefficients down by 1**.
(Lemma lem.fps.laure.xa, label: lem.fps.laure.xa)

If `a = (aₙ)_{n∈ℤ}` is a Laurent polynomial, then `T · a = (aₙ₋₁)_{n∈ℤ}`.
In other words, the coefficient at position `n` in `T * a` equals the coefficient
at position `n - 1` in `a`. -/
lemma T_mul_coeff (a : K[T;T⁻¹]) (n : ℤ) :
    (T 1 * a : K[T;T⁻¹]) n = a (n - 1) := by
  simp only [T, AddMonoidAlgebra.coeff_single_mul_apply, one_mul]
  ring_nf

/-- **Multiplication by T⁻¹ shifts coefficients up by 1**.
(Lemma lem.fps.laure.xa, label: lem.fps.laure.xa)

If `a = (aₙ)_{n∈ℤ}` is a Laurent polynomial, then `T⁻¹ · a = (aₙ₊₁)_{n∈ℤ}`.
In other words, the coefficient at position `n` in `T(-1) * a` equals the coefficient
at position `n + 1` in `a`. -/
lemma T_neg_one_mul_coeff (a : K[T;T⁻¹]) (n : ℤ) :
    (T (-1) * a : K[T;T⁻¹]) n = a (n + 1) := by
  simp only [T, AddMonoidAlgebra.coeff_single_mul_apply, one_mul]
  ring_nf

/-- Multiplication on the right by T also shifts coefficients. -/
lemma mul_T_coeff (a : K[T;T⁻¹]) (n : ℤ) :
    (a * T 1 : K[T;T⁻¹]) n = a (n - 1) := by
  rw [mul_comm, T_mul_coeff]

/-- Multiplication on the right by T⁻¹ also shifts coefficients. -/
lemma mul_T_neg_one_coeff (a : K[T;T⁻¹]) (n : ℤ) :
    (a * T (-1) : K[T;T⁻¹]) n = a (n + 1) := by
  rw [mul_comm, T_neg_one_mul_coeff]

end ShiftByT


section PowersOfT

variable {K : Type*} [CommRing K]

/-- **The k-th power of T is the unit sequence at k**.
(Proposition prop.fps.laure.xk, label: prop.fps.laure.xk)

For each `k ∈ ℤ`, the Laurent polynomial `T(k)` has coefficient 1 at position k
and 0 everywhere else. -/
lemma T_coeff_eq (k : ℤ) (i : ℤ) :
    (T k : K[T;T⁻¹]) i = if i = k then 1 else 0 := by
  change (T k : K[T;T⁻¹]).coeff i = _
  rw [T_apply]
  simp [eq_comm]

/-- `T(k)` is the Kronecker delta at k, restated. -/
lemma T_eq_single (k : ℤ) : (T k : K[T;T⁻¹]) = AddMonoidAlgebra.single k 1 := rfl

/-- The product `T(m) * T(n) = T(m + n)` follows from the group structure. -/
lemma T_mul_T (m n : ℤ) : (T m : K[T;T⁻¹]) * T n = T (m + n) :=
  (T_add m n).symm

/-- For natural number powers, `(T 1)^n = T n`.
(Part of Proposition prop.fps.laure.xk) -/
lemma T_one_pow (n : ℕ) : (T 1 : K[T;T⁻¹]) ^ n = T n := by
  rw [T_pow]
  simp

/-- Helper lemma: the unit associated to `T 1` has inverse `T (-1)`. -/
lemma isUnit_T_one_unit_eq :
    (isUnit_T (R := K) 1).unit =
    ⟨T 1, T (-1), by rw [← T_add]; simp, by rw [← T_add]; simp⟩ := by
  ext
  simp [IsUnit.unit_spec]

/-- **The k-th power of x equals T(k) for all integers k**.
(Proposition prop.fps.laure.xk, label: prop.fps.laure.xk)

This is the key result showing that `x^k = (δᵢ,ₖ)_{i∈ℤ}` for all `k ∈ ℤ`.
Since `T 1` represents `x` and `T k` represents the Kronecker delta at k,
this theorem shows that integer powers of x give the expected sequences.

For natural number powers, this follows from `T_pow`. For negative powers,
we use the fact that `T 1` is a unit with inverse `T (-1)`. -/
lemma T_one_zpow (k : ℤ) : (↑((isUnit_T (R := K) 1).unit ^ k) : K[T;T⁻¹]) = T k := by
  induction k using Int.induction_on with
  | zero =>
    simp only [zpow_zero, Units.val_one]
    rfl
  | succ n ih =>
    rw [zpow_add_one, Units.val_mul, ih, IsUnit.unit_spec, ← T_add]
  | pred n ih =>
    rw [zpow_sub_one, Units.val_mul, ih]
    have hinv : ((isUnit_T (R := K) 1).unit⁻¹ : K[T;T⁻¹]ˣ).val = T (-1) := by
      rw [isUnit_T_one_unit_eq]
      simp
    rw [hinv, ← T_add]
    norm_cast

/-- Corollary: The coefficient of `x^k` at position `i` is `δᵢ,ₖ`.
(Proposition prop.fps.laure.xk, restated in terms of coefficients) -/
lemma T_one_zpow_coeff (k i : ℤ) :
    ((isUnit_T (R := K) 1).unit ^ k : K[T;T⁻¹]ˣ).val i = if i = k then 1 else 0 := by
  rw [T_one_zpow, T_coeff_eq]

end PowersOfT


section Representation

variable {K : Type*} [CommRing K]

/-- **Every Laurent polynomial is a sum of monomials**.

Any Laurent polynomial `a` can be written as `∑_{i ∈ support(a)} aᵢ · Tⁱ`. -/
lemma eq_sum_T (a : K[T;T⁻¹]) :
    a = a.support.sum fun i => C (a i) * T i := by
  conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single a]
  apply Finset.sum_congr rfl
  intro i _
  exact single_eq_C_mul_T (a i) i

/-- Alternative form: every Laurent polynomial is a sum over its support. -/
lemma eq_sum_single (a : K[T;T⁻¹]) :
    a = a.support.sum fun i => AddMonoidAlgebra.single i (a i) :=
  (AddMonoidAlgebra.sum_coeff_single a).symm

end Representation


section LaurentSeriesBasics

variable {K : Type*} [CommRing K]

/-- The variable `X` in Laurent series (as single 1 1) is a unit. -/
lemma LaurentSeries_X_isUnit : IsUnit (HahnSeries.single (1 : ℤ) (1 : K)) := by
  refine ⟨⟨single 1 1, single (-1) 1, ?_, ?_⟩, rfl⟩
  all_goals simp only [single_mul_single, add_neg_cancel, neg_add_cancel, mul_one]; rfl

/-- **Every Laurent series is a sum of monomials**.
(Proposition prop.fps.laure.a=sumaixi, label: prop.fps.laure.a=sumaixi)

Any Laurent series `a` can be written as `∑_{i ∈ ℤ} aᵢ · xⁱ` where the sum
is taken over the support of `a`. This is the infinite sum version of `eq_sum_T`
for Laurent polynomials.

In Mathlib notation, we express this using `SummableFamily.hsum`, which represents
a formal infinite sum of Hahn series. -/
lemma laurentSeries_eq_hsum_single (x : LaurentSeries K) :
    x = (singleFamily x).hsum := by
  ext n
  simp only [SummableFamily.coeff_hsum]
  by_cases hn : x.coeff n = 0
  · -- If x.coeff n = 0, then the finsum is also 0
    rw [hn]
    symm
    apply finsum_eq_zero_of_forall_eq_zero
    intro ⟨g, hg⟩
    simp only [singleFamily, SummableFamily.coe_mk, coeff_single]
    split_ifs with heq
    · subst heq
      exact hn
    · rfl
  · -- If x.coeff n ≠ 0, then n is in the support
    have hn_supp : n ∈ x.support := by simpa [mem_support] using hn
    rw [finsum_eq_single (fun i => (singleFamily x i).coeff n) ⟨n, hn_supp⟩]
    · simp [singleFamily]
    · intro ⟨g, hg⟩ hne
      simp only [singleFamily, SummableFamily.coe_mk, coeff_single]
      simp only [ne_eq, Subtype.mk.injEq] at hne
      split_ifs with heq
      · exact (hne heq.symm).elim
      · rfl

/-- The coefficient version of `laurentSeries_eq_hsum_single`:
the n-th coefficient of a Laurent series equals the finsum of the n-th coefficients
of the single monomials. -/
lemma laurentSeries_coeff_eq_finsum_single (x : LaurentSeries K) (n : ℤ) :
    x.coeff n = ∑ᶠ (i : x.support), (single (i : ℤ) (x.coeff i)).coeff n := by
  conv_lhs => rw [laurentSeries_eq_hsum_single x]
  rfl

end LaurentSeriesBasics


section MultiplicationClosure

variable {K : Type*} [CommRing K]

/-- If `f` and `g` are nonzero Laurent series with orders `p` and `q` respectively,
then `f * g` has order at least `p + q`.

This is the key lemma showing closure under multiplication.
(Part of proof of Theorem thm.fps.laure.lauser-ring) -/
lemma order_mul_ge (f g : LaurentSeries K) :
    f.orderTop + g.orderTop ≤ (f * g).orderTop :=
  HahnSeries.orderTop_add_le_mul

/-- The product of two Laurent series has coefficients zero below the sum of their orders.

This formalizes the key step in the proof: if `aᵢ = 0` for `i < p` and `bⱼ = 0` for `j < q`,
then `cₙ = 0` for `n < p + q`.
(Part of proof of Theorem thm.fps.laure.lauser-ring) -/
lemma coeff_mul_eq_zero_of_lt_order (f g : LaurentSeries K) (n : ℤ)
    (hn : n < f.order + g.order) (hf : f ≠ 0) (hg : g ≠ 0) : (f * g).coeff n = 0 := by
  by_cases hfg : f * g = 0
  · simp [hfg]
  · apply HahnSeries.coeff_eq_zero_of_lt_order
    have h := HahnSeries.orderTop_add_le_mul (x := f) (y := g)
    rw [HahnSeries.orderTop_of_ne_zero hf, HahnSeries.orderTop_of_ne_zero hg,
        HahnSeries.orderTop_of_ne_zero hfg] at h
    norm_cast at h
    rw [HahnSeries.order_of_ne hf, HahnSeries.order_of_ne hg] at hn
    rw [HahnSeries.order_of_ne hfg]
    exact lt_of_lt_of_le hn h

end MultiplicationClosure


section PowerSeriesEmbedding

variable {K : Type*} [CommRing K]

/-- The embedding preserves the ring structure. -/
lemma powerSeriesToLaurent_injective : Function.Injective (powerSeriesToLaurent (K := K)) :=
  HahnSeries.ofPowerSeries_injective

/-- Coefficients are preserved for non-negative indices. -/
lemma coeff_powerSeriesToLaurent (f : PowerSeries K) (n : ℕ) :
    (powerSeriesToLaurent f).coeff n = PowerSeries.coeff n f :=
  LaurentSeries.coeff_coe_powerSeries f n

end PowerSeriesEmbedding


section LaurentPolynomialEmbedding

variable {K : Type*} [CommRing K]

/-- The embedding is additive. -/
lemma laurentPolynomialToSeries_add (p q : K[T;T⁻¹]) :
    laurentPolynomialToSeries (p + q) =
    laurentPolynomialToSeries p + laurentPolynomialToSeries q := by
  ext n
  simp only [laurentPolynomialToSeries, HahnSeries.coeff_add', Pi.add_apply]
  rfl

/-- The embedding sends 0 to 0. -/
lemma laurentPolynomialToSeries_zero :
    laurentPolynomialToSeries (0 : K[T;T⁻¹]) = 0 := by
  ext n
  simp only [laurentPolynomialToSeries, HahnSeries.coeff_zero]
  rfl

/-- The embedding sends 1 to 1. -/
lemma laurentPolynomialToSeries_one :
    laurentPolynomialToSeries (1 : K[T;T⁻¹]) = 1 := by
  ext n
  simp only [laurentPolynomialToSeries, HahnSeries.coeff_one]
  simp

/-- The embedding is multiplicative. -/
lemma laurentPolynomialToSeries_mul (p q : K[T;T⁻¹]) :
    laurentPolynomialToSeries (p * q) =
    laurentPolynomialToSeries p * laurentPolynomialToSeries q := by
  ext n
  rw [HahnSeries.coeff_mul]
  -- The Hahn series antidiagonal equals the filtered product of supports
  have hs_eq : Finset.antidiagonal
      (laurentPolynomialToSeries p).isPWO_support
      (laurentPolynomialToSeries q).isPWO_support n =
      (p.support ×ˢ q.support).filter (fun ij => ij.1 + ij.2 = n) := by
    ext ⟨i, j⟩
    simp only [Finset.mem_antidiagonal, AddMonoidAlgebra.support, Finsupp.mem_support_iff,
               Finset.mem_filter, Finset.mem_product, laurentPolynomialToSeries, HahnSeries.mem_support]
    simp [and_assoc]
  rw [hs_eq]
  classical
  simp only [laurentPolynomialToSeries, AddMonoidAlgebra.mul_apply, Finsupp.sum,
    Finset.sum_filter, Finset.sum_product]
  simp [AddMonoidAlgebra.support]

/-- The embedding preserves coefficients. -/
lemma laurentPolynomialToSeries_coeff (p : K[T;T⁻¹]) (n : ℤ) :
    (laurentPolynomialToSeries p).coeff n = p n := rfl

end LaurentPolynomialEmbedding


section BinaryRepresentation

open Finset in

/-- Every natural number has a binary representation.
(Existence part of Theorem thm.fps.laure.binary-rep-uniq) -/
lemma exists_binaryRepresentation (n : ℕ) : ∃ s : Finset ℕ, BinaryRepresentation n s :=
  ⟨n.bitIndices.toFinset, by simp [BinaryRepresentation, List.sum_toFinset _ Nat.bitIndices_nodup]⟩

/-- The binary representation is unique.
(Uniqueness part of Theorem thm.fps.laure.binary-rep-uniq) -/
lemma binaryRepresentation_unique {n : ℕ} {s t : Finset ℕ}
    (hs : BinaryRepresentation n s) (ht : BinaryRepresentation n t) : s = t := by
  simp only [BinaryRepresentation] at hs ht
  exact Finset.geomSum_injective (by norm_num : 2 ≤ 2) (hs.symm.trans ht)

/-- **Unique Binary Representation Theorem**.
(Theorem thm.fps.laure.binary-rep-uniq, label: thm.fps.laure.binary-rep-uniq)

Each natural number `n` has a unique binary representation. More precisely, there exists
a unique finset `s ⊆ ℕ` such that `n = ∑_{i ∈ s} 2^i`.

This is a fundamental result that motivates the study of Laurent series: when trying to
prove the analogous result for balanced ternary representations (where coefficients can
be -1, 0, or 1), we need to work with negative powers of the base, which leads naturally
to Laurent series. -/
lemma binaryRepresentation_exists_unique (n : ℕ) :
    ∃! s : Finset ℕ, BinaryRepresentation n s := by
  use n.bitIndices.toFinset
  constructor
  · simp [BinaryRepresentation, List.sum_toFinset _ Nat.bitIndices_nodup]
  · intro t ht
    simp only [BinaryRepresentation] at ht
    have h1 : n = ∑ i ∈ n.bitIndices.toFinset, 2 ^ i := by
      simp [List.sum_toFinset _ Nat.bitIndices_nodup]
    exact Finset.geomSum_injective (by norm_num : 2 ≤ 2) (ht.symm.trans h1)

/-- The canonical binary representation satisfies the defining property. -/
lemma canonicalBinaryRep_spec (n : ℕ) : BinaryRepresentation n (canonicalBinaryRep n) := by
  simp [BinaryRepresentation, canonicalBinaryRep, List.sum_toFinset _ Nat.bitIndices_nodup]

/-- The canonical binary representation is the unique one. -/
lemma canonicalBinaryRep_eq_of_binaryRepresentation {n : ℕ} {s : Finset ℕ}
    (hs : BinaryRepresentation n s) : s = canonicalBinaryRep n :=
  binaryRepresentation_unique hs (canonicalBinaryRep_spec n)

/-- The equivalence sends `n` to its canonical binary representation. -/
lemma binaryRepEquiv_apply (n : ℕ) : binaryRepEquiv n = canonicalBinaryRep n := rfl

/-- The inverse of the equivalence computes the sum `∑_{i ∈ s} 2^i`. -/
lemma binaryRepEquiv_symm_apply (s : Finset ℕ) : binaryRepEquiv.symm s = ∑ i ∈ s, 2 ^ i := rfl

/-- Round-trip: converting to binary representation and back gives the original number. -/
lemma binaryRepEquiv_left_inv (n : ℕ) : binaryRepEquiv.symm (binaryRepEquiv n) = n :=
  binaryRepEquiv.symm_apply_apply n

/-- Round-trip: converting from binary representation and back gives the original finset. -/
lemma binaryRepEquiv_right_inv (s : Finset ℕ) : binaryRepEquiv (binaryRepEquiv.symm s) = s :=
  binaryRepEquiv.apply_symm_apply s

end BinaryRepresentation


section BalancedTernaryRepresentation

open Finset

lemma btDigits_card : btDigits.card = 3 := by decide

lemma mem_btDigits_iff (b : ℤ) : b ∈ btDigits ↔ b = -1 ∨ b = 0 ∨ b = 1 := by
  simp [btDigits]

/-- The number of k-bounded balanced ternary representations is 3^{k+1}. -/
lemma card_kBoundedBTReps (k : ℕ) : (kBoundedBTReps k).card = 3 ^ (k + 1) := by
  unfold kBoundedBTReps
  rw [Fintype.card_piFinset]
  simp [Finset.prod_const, btDigits_card]

/-- Key identity: `2 * M_k + 1 = 3^{k+1}`. -/
lemma maxBT_eq (k : ℕ) : 2 * maxBT k + 1 = 3 ^ (k + 1) := by
  unfold maxBT
  induction k with
  | zero => norm_num
  | succ n ih =>
    rw [sum_range_succ, mul_add]
    calc 2 * ∑ x ∈ range (n + 1), 3 ^ x + 2 * 3 ^ (n + 1) + 1
        = (2 * ∑ x ∈ range (n + 1), 3 ^ x + 1) + 2 * 3 ^ (n + 1) := by ring
      _ = 3 ^ (n + 1) + 2 * 3 ^ (n + 1) := by rw [ih]
      _ = 3 * 3 ^ (n + 1) := by ring
      _ = 3 ^ (n + 1 + 1) := by ring_nf

/-- The cardinality of `Icc (-M) M` is `2M + 1`. -/
lemma card_Icc_symm (M : ℕ) : (Icc_symm M).card = 2 * M + 1 := by
  unfold Icc_symm
  rw [Int.card_Icc]
  omega

/-- Cardinality of `Icc_symm (maxBT k)` equals `3^{k+1}`. -/
lemma card_Icc_symm_maxBT (k : ℕ) : (Icc_symm (maxBT k)).card = 3 ^ (k + 1) := by
  rw [card_Icc_symm, maxBT_eq]

/-- Helper for the bounds: sum of 3^i over Fin (k+1) equals sum over range (k+1). -/
lemma sum_pow_three_Fin_eq_range (k : ℕ) :
    (∑ i : Fin (k + 1), (3 : ℤ) ^ (i : ℕ)) = ∑ i ∈ range (k + 1), (3 : ℤ) ^ i :=
  Fin.sum_univ_eq_sum_range (fun i => (3 : ℤ) ^ i) (k + 1)

/-- The value of any k-bounded representation is in `[-M_k, M_k]`. -/
lemma kBoundedBTValue_mem_Icc (k : ℕ) (f : Fin (k + 1) → ℤ) (hf : f ∈ kBoundedBTReps k) :
    kBoundedBTValue k f ∈ Icc_symm (maxBT k) := by
  unfold kBoundedBTValue Icc_symm maxBT
  simp only [mem_Icc]
  have hf' : ∀ i, f i = -1 ∨ f i = 0 ∨ f i = 1 := fun i => by
    simp only [kBoundedBTReps, Fintype.mem_piFinset] at hf
    exact (mem_btDigits_iff _).mp (hf i)
  constructor
  · -- Lower bound: -M_k ≤ value
    have h : ∑ i : Fin (k + 1), (-1 : ℤ) * (3 : ℤ) ^ (i : ℕ) ≤ ∑ i : Fin (k + 1), f i * (3 : ℤ) ^ (i : ℕ) := by
      apply sum_le_sum
      intro i _
      have h3pos : (0 : ℤ) < (3 : ℤ) ^ (i : ℕ) := pow_pos (by norm_num) _
      rcases hf' i with hi | hi | hi <;> simp only [hi] <;> linarith
    have heq : ∑ i : Fin (k + 1), (-1 : ℤ) * (3 : ℤ) ^ (i : ℕ) = -(∑ i : Fin (k + 1), (3 : ℤ) ^ (i : ℕ)) := by
      rw [← sum_neg_distrib]
      congr 1
      ext i
      ring
    rw [heq, sum_pow_three_Fin_eq_range] at h
    simp only [Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat] at h ⊢
    exact h
  · -- Upper bound: value ≤ M_k
    have h : ∑ i : Fin (k + 1), f i * (3 : ℤ) ^ (i : ℕ) ≤ ∑ i : Fin (k + 1), (1 : ℤ) * (3 : ℤ) ^ (i : ℕ) := by
      apply sum_le_sum
      intro i _
      have h3pos : (0 : ℤ) < (3 : ℤ) ^ (i : ℕ) := pow_pos (by norm_num) _
      rcases hf' i with hi | hi | hi <;> simp only [hi] <;> linarith
    have heq : ∑ i : Fin (k + 1), (1 : ℤ) * (3 : ℤ) ^ (i : ℕ) = ∑ i : Fin (k + 1), (3 : ℤ) ^ (i : ℕ) := by
      congr 1
      ext i
      ring
    rw [heq, sum_pow_three_Fin_eq_range] at h
    simp only [Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat] at h ⊢
    exact h

/-- If two balanced ternary representations have the same value, they are equal.

This is the key injectivity lemma for balanced ternary representations.
The proof uses a mod 3 argument at each digit position:
- The lowest digit determines the value mod 3
- Subtracting the lowest digit and dividing by 3 gives a smaller representation
- By strong induction, the remaining digits must also be equal. -/
lemma balanced_ternary_injective (k : ℕ) (f g : Fin (k + 1) → ℤ)
    (hf : ∀ i, f i = -1 ∨ f i = 0 ∨ f i = 1)
    (hg : ∀ i, g i = -1 ∨ g i = 0 ∨ g i = 1)
    (hfg : ∑ i : Fin (k + 1), f i * (3 : ℤ) ^ (i : ℕ) =
           ∑ i : Fin (k + 1), g i * (3 : ℤ) ^ (i : ℕ)) :
    f = g := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    cases k with
    | zero =>
      ext i
      fin_cases i
      have h1 : (∑ i : Fin 1, f i * (3 : ℤ) ^ (i : ℕ)) = f 0 := by simp
      have h2 : (∑ i : Fin 1, g i * (3 : ℤ) ^ (i : ℕ)) = g 0 := by simp
      rw [h1, h2] at hfg
      exact hfg
    | succ n =>
      have h0 : f 0 = g 0 := by
        have hf_mod : (∑ i : Fin (n + 2), f i * (3 : ℤ) ^ (i : ℕ)) % 3 = f 0 % 3 := by
          have : ∑ i : Fin (n + 2), f i * (3 : ℤ) ^ (i : ℕ) = f 0 +
                 ∑ i : Fin (n + 1), f i.succ * (3 : ℤ) ^ (i.val + 1) := by
            rw [Fin.sum_univ_succ]
            simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ]
          rw [this]
          have hdiv : (3 : ℤ) ∣ ∑ i : Fin (n + 1), f i.succ * (3 : ℤ) ^ (i.val + 1) := by
            apply dvd_sum
            intro i _
            rw [pow_succ]
            exact dvd_mul_of_dvd_right (dvd_mul_left _ _) _
          obtain ⟨c, hc⟩ := hdiv
          rw [hc]
          omega
        have hg_mod : (∑ i : Fin (n + 2), g i * (3 : ℤ) ^ (i : ℕ)) % 3 = g 0 % 3 := by
          have : ∑ i : Fin (n + 2), g i * (3 : ℤ) ^ (i : ℕ) = g 0 +
                 ∑ i : Fin (n + 1), g i.succ * (3 : ℤ) ^ (i.val + 1) := by
            rw [Fin.sum_univ_succ]
            simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ]
          rw [this]
          have hdiv : (3 : ℤ) ∣ ∑ i : Fin (n + 1), g i.succ * (3 : ℤ) ^ (i.val + 1) := by
            apply dvd_sum
            intro i _
            rw [pow_succ]
            exact dvd_mul_of_dvd_right (dvd_mul_left _ _) _
          obtain ⟨c, hc⟩ := hdiv
          rw [hc]
          omega
        rw [hfg] at hf_mod
        have hmod_eq : f 0 % 3 = g 0 % 3 := hf_mod.symm.trans hg_mod
        rcases hf 0 with hf0 | hf0 | hf0 <;> rcases hg 0 with hg0 | hg0 | hg0 <;>
          simp only [hf0, hg0] at hmod_eq ⊢ <;> omega
      ext ⟨i, hi⟩
      cases i with
      | zero => exact h0
      | succ j =>
        let f' : Fin (n + 1) → ℤ := fun i => f i.succ
        let g' : Fin (n + 1) → ℤ := fun i => g i.succ
        have hf' : ∀ i, f' i = -1 ∨ f' i = 0 ∨ f' i = 1 := fun i => hf i.succ
        have hg' : ∀ i, g' i = -1 ∨ g' i = 0 ∨ g' i = 1 := fun i => hg i.succ
        have hfg' : ∑ i : Fin (n + 1), f' i * (3 : ℤ) ^ (i : ℕ) =
                    ∑ i : Fin (n + 1), g' i * (3 : ℤ) ^ (i : ℕ) := by
          have hsum_f : ∑ i : Fin (n + 2), f i * (3 : ℤ) ^ (i : ℕ) =
                        f 0 + 3 * ∑ i : Fin (n + 1), f' i * (3 : ℤ) ^ (i : ℕ) := by
            rw [Fin.sum_univ_succ]
            simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, f']
            rw [mul_sum]
            congr 1
            apply sum_congr rfl
            intro i _
            ring
          have hsum_g : ∑ i : Fin (n + 2), g i * (3 : ℤ) ^ (i : ℕ) =
                        g 0 + 3 * ∑ i : Fin (n + 1), g' i * (3 : ℤ) ^ (i : ℕ) := by
            rw [Fin.sum_univ_succ]
            simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, g']
            rw [mul_sum]
            congr 1
            apply sum_congr rfl
            intro i _
            ring
          rw [hsum_f, hsum_g, h0] at hfg
          linarith
        have heq : f' = g' := ih n (by omega) f' g' hf' hg' hfg'
        have hj : j < n + 1 := by omega
        have hsucc : f' ⟨j, hj⟩ = g' ⟨j, hj⟩ := congrFun heq ⟨j, hj⟩
        simpa [f', g', Fin.succ_mk] using hsucc

/-- kBoundedBTValue is injective on kBoundedBTReps. -/
lemma kBoundedBTValue_injective_on (k : ℕ) :
    Set.InjOn (kBoundedBTValue k) (kBoundedBTReps k : Set (Fin (k + 1) → ℤ)) := by
  intro f hf g hg hfg
  have hf' : ∀ i, f i = -1 ∨ f i = 0 ∨ f i = 1 := fun i => by
    have : f ∈ kBoundedBTReps k := hf
    simp only [kBoundedBTReps, Fintype.mem_piFinset] at this
    exact (mem_btDigits_iff _).mp (this i)
  have hg' : ∀ i, g i = -1 ∨ g i = 0 ∨ g i = 1 := fun i => by
    have : g ∈ kBoundedBTReps k := hg
    simp only [kBoundedBTReps, Fintype.mem_piFinset] at this
    exact (mem_btDigits_iff _).mp (this i)
  exact balanced_ternary_injective k f g hf' hg' hfg

/-- **Each integer in `[-M_k, M_k]` has a unique k-bounded balanced ternary representation**.

This is the finite version of the balanced ternary uniqueness theorem.

The proof uses a cardinality argument:
- There are `3^{k+1}` k-bounded representations (`card_kBoundedBTReps`)
- The target set `Icc_symm (maxBT k)` has cardinality `3^{k+1}` (`card_Icc_symm_maxBT`)
- Each representation maps to a value in the target set (`kBoundedBTValue_mem_Icc`)
- By the pigeonhole principle, the map is a bijection

(Part of Theorem thm.fps.laure.balanced-tern-rep-uniq) -/
lemma kBounded_unique (k : ℕ) (n : ℤ) (hn : n ∈ Icc_symm (maxBT k)) :
    ∃! f ∈ kBoundedBTReps k, kBoundedBTValue k f = n := by
  -- The map from kBoundedBTReps to Icc_symm is a bijection by cardinality
  have h_card_eq : (kBoundedBTReps k).card = (Icc_symm (maxBT k)).card := by
    rw [card_kBoundedBTReps, card_Icc_symm_maxBT]
  have h_image_subset : (kBoundedBTReps k).image (kBoundedBTValue k) ⊆ Icc_symm (maxBT k) := by
    intro x hx
    simp only [mem_image] at hx
    obtain ⟨f, hf, rfl⟩ := hx
    exact kBoundedBTValue_mem_Icc k f hf
  -- The image has the same cardinality as kBoundedBTReps because the map is injective
  have h_card_image : ((kBoundedBTReps k).image (kBoundedBTValue k)).card = (kBoundedBTReps k).card := by
    rw [card_image_of_injOn (kBoundedBTValue_injective_on k)]
  -- So the image equals Icc_symm
  have h_image_eq : (kBoundedBTReps k).image (kBoundedBTValue k) = Icc_symm (maxBT k) := by
    apply eq_of_subset_of_card_le h_image_subset
    rw [h_card_image, h_card_eq]
  -- Existence: n is in the image
  have h_exists : ∃ f ∈ kBoundedBTReps k, kBoundedBTValue k f = n := by
    rw [← h_image_eq] at hn
    simp only [mem_image] at hn
    exact hn
  -- Uniqueness: from injectivity
  obtain ⟨f, hf_mem, hf_val⟩ := h_exists
  use f
  constructor
  · exact ⟨hf_mem, hf_val⟩
  · intro g ⟨hg_mem, hg_val⟩
    exact (kBoundedBTValue_injective_on k hf_mem hg_mem (hf_val.trans hg_val.symm)).symm

lemma kBoundedToFinsupp_apply (k : ℕ) (f : Fin (k + 1) → ℤ) (i : ℕ) (hi : i < k + 1) :
    kBoundedToFinsupp k f i = f ⟨i, hi⟩ := by
  simp only [kBoundedToFinsupp, Finsupp.onFinset_apply, hi, dite_true]

lemma kBoundedToFinsupp_apply_of_ge (k : ℕ) (f : Fin (k + 1) → ℤ) (i : ℕ) (hi : k + 1 ≤ i) :
    kBoundedToFinsupp k f i = 0 := by
  simp only [kBoundedToFinsupp, Finsupp.onFinset_apply]
  simp only [not_lt.mpr hi, dite_false]

/-- The sum over kBoundedToFinsupp equals kBoundedBTValue. -/
lemma kBoundedToFinsupp_sum (k : ℕ) (f : Fin (k + 1) → ℤ) :
    ∑ i ∈ (kBoundedToFinsupp k f).support, (kBoundedToFinsupp k f) i * (3 : ℤ) ^ i = kBoundedBTValue k f := by
  unfold kBoundedBTValue
  have hsup : (kBoundedToFinsupp k f).support ⊆ range (k + 1) := by
    intro i hi
    simp only [Finsupp.mem_support_iff] at hi
    by_contra h
    simp only [mem_range, not_lt] at h
    rw [kBoundedToFinsupp_apply_of_ge k f i h] at hi
    exact hi rfl
  rw [sum_subset hsup]
  · rw [sum_range (fun i => (kBoundedToFinsupp k f) i * (3 : ℤ) ^ i)]
    apply sum_congr rfl
    intro i _
    rw [kBoundedToFinsupp_apply k f i i.isLt]
  · intro i _ hi
    rw [Finsupp.notMem_support_iff.mp hi]
    ring

/-- **Every integer has a balanced ternary representation**.
(Existence part of Theorem thm.fps.laure.balanced-tern-rep-uniq)

For any integer n, we can find k large enough that |n| ≤ M_k, then use
the k-bounded existence result. -/
lemma balancedTernary_exists (n : ℤ) : Nonempty (BalancedTernaryRep n) := by
  -- Find k such that |n| ≤ maxBT k
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (|n| : ℤ) ≤ maxBT k := by
    use n.natAbs
    have h3 : n.natAbs ≤ maxBT n.natAbs := by
      unfold maxBT
      have h1 : n.natAbs < 3 ^ n.natAbs :=
        Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_left (by norm_num : 2 ≤ 3) n.natAbs)
      have h2 : (3 : ℕ) ^ n.natAbs ≤ ∑ i ∈ range (n.natAbs + 1), 3 ^ i := by
        apply single_le_sum (fun i _ => Nat.zero_le _)
        exact mem_range.mpr (Nat.lt_succ_self _)
      omega
    simp only [Int.abs_eq_natAbs]
    exact Int.ofNat_le.mpr h3
  -- Show that n ∈ Icc_symm (maxBT k)
  have hn_mem : n ∈ Icc_symm (maxBT k) := by
    simp only [Icc_symm, mem_Icc]
    constructor
    · calc -(maxBT k : ℤ) ≤ -|n| := by omega
        _ ≤ n := neg_abs_le n
    · calc n ≤ |n| := le_abs_self n
        _ ≤ maxBT k := hk
  -- Use kBounded_unique to get existence
  obtain ⟨f, ⟨hf_mem, hf_val⟩, _⟩ := kBounded_unique k n hn_mem
  -- Convert f to a BalancedTernaryRep
  let digits : ℕ →₀ ℤ := kBoundedToFinsupp k f
  have hdigits_range : ∀ i, digits i ∈ btDigits := by
    intro i
    by_cases hi : i < k + 1
    · rw [kBoundedToFinsupp_apply k f i hi]
      simp only [kBoundedBTReps, Fintype.mem_piFinset] at hf_mem
      exact hf_mem ⟨i, hi⟩
    · rw [kBoundedToFinsupp_apply_of_ge k f i (by omega)]
      simp [btDigits]
  have hsum_eq : ∑ i ∈ digits.support, digits i * (3 : ℤ) ^ i = n := by
    rw [kBoundedToFinsupp_sum k f, hf_val]
  exact ⟨⟨digits, hdigits_range, hsum_eq⟩⟩

/-- Key lemma: 2 * ∑_{i<k} 3^i < 3^k. -/
lemma two_sum_lt_pow_three (k : ℕ) : 2 * ∑ i ∈ range k, (3 : ℤ) ^ i < 3 ^ k := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, mul_add, pow_succ]
    have h : 2 * ∑ x ∈ range n, (3 : ℤ) ^ x < 3 ^ n := ih
    nlinarith [pow_nonneg (by norm_num : (0 : ℤ) ≤ 3) n]

/-- The sum over a superset equals the sum over the support (for finitely supported functions). -/
lemma sum_eq_sum_support' (f : ℕ →₀ ℤ) (s : Finset ℕ) (hs : f.support ⊆ s) :
    ∑ i ∈ s, f i * (3 : ℤ) ^ i = ∑ i ∈ f.support, f i * (3 : ℤ) ^ i := by
  symm
  apply sum_subset hs
  intro i _ hi
  simp only [Finsupp.mem_support_iff, ne_eq, not_not] at hi
  simp [hi]

/-- If a, b ∈ {-1, 0, 1} and a ≠ b, then |a - b| ≥ 1. -/
lemma btDigits_diff_abs_ge_one {a b : ℤ} (ha : a ∈ btDigits) (hb : b ∈ btDigits) (hab : a ≠ b) :
    |a - b| ≥ 1 := by
  simp only [btDigits, mem_insert, mem_singleton] at ha hb
  rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;>
    simp only [ha, hb] at hab ⊢ <;> try norm_num
  all_goals exact absurd rfl hab

/-- If a, b ∈ {-1, 0, 1}, then |a - b| ≤ 2. -/
lemma btDigits_diff_abs_le_two {a b : ℤ} (ha : a ∈ btDigits) (hb : b ∈ btDigits) :
    |a - b| ≤ 2 := by
  simp only [btDigits, mem_insert, mem_singleton] at ha hb
  rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;>
    simp only [ha, hb] <;> norm_num

/-- Two finitely supported functions with values in btDigits and the same weighted sum are equal. -/
lemma btDigits_sum_unique (f g : ℕ →₀ ℤ) 
    (hf : ∀ i, f i ∈ btDigits) (hg : ∀ i, g i ∈ btDigits)
    (hsum : ∑ i ∈ f.support, f i * (3 : ℤ) ^ i = ∑ i ∈ g.support, g i * (3 : ℤ) ^ i) :
    f = g := by
  by_contra hne
  have hdiff : ∃ i, f i ≠ g i := by
    by_contra hall
    push Not at hall
    exact hne (Finsupp.ext hall)
  let S := f.support ∪ g.support
  have hf_sum : ∑ i ∈ S, f i * (3 : ℤ) ^ i = ∑ i ∈ f.support, f i * (3 : ℤ) ^ i := 
    sum_eq_sum_support' f S (subset_union_left)
  have hg_sum : ∑ i ∈ S, g i * (3 : ℤ) ^ i = ∑ i ∈ g.support, g i * (3 : ℤ) ^ i := 
    sum_eq_sum_support' g S (subset_union_right)
  have hdiff_sum : ∑ i ∈ S, (f i - g i) * (3 : ℤ) ^ i = 0 := by
    have : ∑ i ∈ S, (f i - g i) * (3 : ℤ) ^ i = 
           ∑ i ∈ S, f i * (3 : ℤ) ^ i - ∑ i ∈ S, g i * (3 : ℤ) ^ i := by
      rw [← sum_sub_distrib]
      congr 1
      ext i
      ring
    rw [this, hf_sum, hg_sum, hsum, sub_self]
  let D := S.filter (fun i => f i ≠ g i)
  have hD_nonempty : D.Nonempty := by
    obtain ⟨i, hi⟩ := hdiff
    use i
    simp only [D, mem_filter, S, mem_union, Finsupp.mem_support_iff, ne_eq]
    constructor
    · by_contra h
      push Not at h
      exact hi (h.1.trans h.2.symm)
    · exact hi
  let k := D.max' hD_nonempty
  have hk_mem : k ∈ D := max'_mem D hD_nonempty
  have hk_diff : f k ≠ g k := (mem_filter.mp hk_mem).2
  have hk_max : ∀ i ∈ D, i ≤ k := fun i hi => le_max' D i hi
  have hk_agree : ∀ i ∈ S, k < i → f i = g i := by
    intro i hi hki
    by_contra h
    have : i ∈ D := by simp only [D, mem_filter]; exact ⟨hi, h⟩
    have : i ≤ k := hk_max i this
    omega
  have hk_in_S : k ∈ S := (mem_filter.mp hk_mem).1
  have hsum_eq : ∑ i ∈ S, (f i - g i) * (3 : ℤ) ^ i = 
                 ∑ i ∈ S.filter (· ≤ k), (f i - g i) * (3 : ℤ) ^ i := by
    symm
    apply sum_subset (filter_subset _ _)
    intro i hi hni
    simp only [mem_filter, not_and, not_le] at hni
    have hik : k < i := hni hi
    simp only [hk_agree i hi hik, sub_self, zero_mul]
  rw [hsum_eq] at hdiff_sum
  have hk_in_filter : k ∈ S.filter (· ≤ k) := by
    simp only [mem_filter, le_refl, and_true]
    exact hk_in_S
  have hk_not_in_erase : k ∉ (S.filter (· ≤ k)).erase k := by
    simp only [mem_erase, ne_eq, not_true_eq_false, false_and, not_false_eq_true]
  rw [← insert_erase hk_in_filter, sum_insert hk_not_in_erase] at hdiff_sum
  have herase_subset : (S.filter (· ≤ k)).erase k ⊆ range k := by
    intro i hi
    simp only [mem_erase, mem_filter] at hi
    simp only [mem_range]
    omega
  have hbound : |∑ i ∈ (S.filter (· ≤ k)).erase k, (f i - g i) * (3 : ℤ) ^ i| ≤ 
                2 * ∑ i ∈ range k, (3 : ℤ) ^ i := by
    calc |∑ i ∈ (S.filter (· ≤ k)).erase k, (f i - g i) * (3 : ℤ) ^ i|
        ≤ ∑ i ∈ (S.filter (· ≤ k)).erase k, |(f i - g i) * (3 : ℤ) ^ i| := abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ (S.filter (· ≤ k)).erase k, |f i - g i| * (3 : ℤ) ^ i := by
          congr 1; ext i
          rw [abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℤ) < 3)]
      _ ≤ ∑ i ∈ (S.filter (· ≤ k)).erase k, 2 * (3 : ℤ) ^ i := by
          apply sum_le_sum
          intro i _
          have h := btDigits_diff_abs_le_two (hf i) (hg i)
          have h3pos : (0 : ℤ) < 3 ^ i := pow_pos (by norm_num) i
          nlinarith
      _ ≤ ∑ i ∈ range k, 2 * (3 : ℤ) ^ i := by
          apply sum_le_sum_of_subset_of_nonneg herase_subset
          intro i _ _
          have h3pos : (0 : ℤ) < 3 ^ i := pow_pos (by norm_num) i
          linarith
      _ = 2 * ∑ i ∈ range k, (3 : ℤ) ^ i := by rw [mul_sum]
  have hk_eq : (f k - g k) * (3 : ℤ) ^ k = 
               -∑ i ∈ (S.filter (· ≤ k)).erase k, (f i - g i) * (3 : ℤ) ^ i := by
    linarith
  have habs_eq : |(f k - g k) * (3 : ℤ) ^ k| = 
                 |∑ i ∈ (S.filter (· ≤ k)).erase k, (f i - g i) * (3 : ℤ) ^ i| := by
    rw [hk_eq, abs_neg]
  have hfk_gk_bound : |f k - g k| ≥ 1 := btDigits_diff_abs_ge_one (hf k) (hg k) hk_diff
  have hlower : |(f k - g k) * (3 : ℤ) ^ k| ≥ (3 : ℤ) ^ k := by
    rw [abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℤ) < 3)]
    have h3k_pos : (0 : ℤ) < 3 ^ k := pow_pos (by norm_num) k
    nlinarith
  have hupper : |∑ i ∈ (S.filter (· ≤ k)).erase k, (f i - g i) * (3 : ℤ) ^ i| < (3 : ℤ) ^ k := by
    calc |∑ i ∈ (S.filter (· ≤ k)).erase k, (f i - g i) * (3 : ℤ) ^ i|
        ≤ 2 * ∑ i ∈ range k, (3 : ℤ) ^ i := hbound
      _ < (3 : ℤ) ^ k := two_sum_lt_pow_three k
  rw [habs_eq] at hlower
  linarith

/-- **The balanced ternary representation is unique**.
(Uniqueness part of Theorem thm.fps.laure.balanced-tern-rep-uniq)

If two balanced ternary representations have the same value, they must be equal. -/
lemma balancedTernary_unique (n : ℤ) (r1 r2 : BalancedTernaryRep n) :
    r1.digits = r2.digits := by
  apply btDigits_sum_unique
  · exact r1.digits_range
  · exact r2.digits_range
  · rw [r1.sum_eq, r2.sum_eq]

/-- **Unique Balanced Ternary Representation Theorem**.
(Theorem thm.fps.laure.balanced-tern-rep-uniq, label: thm.fps.laure.balanced-tern-rep-uniq)

Each integer `n` has a unique balanced ternary representation. More precisely, there exists
a unique finitely supported function `f : ℕ → ℤ` with values in {-1, 0, 1} such that
`n = ∑_{i ∈ support(f)} f(i) · 3^i`.

This theorem generalizes the binary representation uniqueness to allow negative digits,
which enables representing negative integers directly (without a separate sign).

The proof uses Laurent polynomials and the key identity:
  `∏_{i=0}^{k} (1 + x^{3^i} + x^{-3^i}) = ∑_{|n| ≤ M_k} x^n`
where `M_k = 3^0 + 3^1 + ... + 3^k = (3^{k+1} - 1) / 2`.

Comparing coefficients shows that each integer in `[-M_k, M_k]` has exactly one
k-bounded balanced ternary representation. Taking `k → ∞` gives the full result.

Historical note: Balanced ternary representations were used in the Soviet Setun computer
(1960s/70s). The uniqueness theorem goes back to Fibonacci. -/
lemma balancedTernary_exists_unique (n : ℤ) :
    ∃! f : ℕ →₀ ℤ, (∀ i, f i ∈ btDigits) ∧ balancedTernaryValue f = n := by
  obtain ⟨rep⟩ := balancedTernary_exists n
  use rep.digits
  constructor
  · exact ⟨rep.digits_range, rep.sum_eq⟩
  · intro f ⟨hf_range, hf_sum⟩
    let rep2 : BalancedTernaryRep n := ⟨f, hf_range, hf_sum⟩
    exact balancedTernary_unique n rep2 rep

end BalancedTernaryRepresentation


section BalancedTernaryEquivalence

/-- The two balanced ternary representations are semantically equivalent: 
they both represent the same integer. -/
lemma balancedTernary_representations_equiv (n : ℤ) :
    (∃ _ : BalancedTernaryRep n, True) ↔ (∃ _ : BTRep n, True) := by
  constructor
  · intro ⟨r, _⟩
    exact ⟨r.toInductive, trivial⟩
  · intro ⟨r, _⟩
    exact ⟨r.toFinsupp, trivial⟩

end BalancedTernaryEquivalence

end AlgebraicCombinatorics.FPS.Laurent

end


/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_laurentPoly_finite_support
  [CommRing K]
-- given
  (p : LaurentPoly K) :
-- imply
  (p.support : Set ℤ).Finite := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.laurentPoly_finite_support p

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_laurentPoly_mul_coeff
  [CommRing K]
-- given
  (a b : LaurentPoly K)
  (n : ℤ) :
-- imply
  (a * b) n = ∑ i ∈ a.support, a i * b (n - i) := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.laurentPoly_mul_coeff a b n

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_laurentPoly_X_coeff
  [CommRing K]
-- given
  (n : ℤ) :
-- imply
  (laurentPoly_X (K := K)) n = if n = 1 then 1 else 0 := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.laurentPoly_X_coeff n

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_laurentPoly_one_coeff
  [CommRing K]
-- given
  (n : ℤ) :
-- imply
  (1 : LaurentPoly K) n = if n = 0 then 1 else 0 := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.laurentPoly_one_coeff n

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_laurentPoly_one_eq_T_zero
  [CommRing K] :
-- imply
  (1 : LaurentPoly K) = T 0 := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.laurentPoly_one_eq_T_zero

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_laurentPoly_smul_coeff
  [CommRing K]
-- given
  (c : K)
  (p : LaurentPoly K)
  (n : ℤ) :
-- imply
  (c • p) n = c * p n := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.laurentPoly_smul_coeff c p n

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_laurentPoly_add_coeff
  [CommRing K]
-- given
  (p q : LaurentPoly K)
  (n : ℤ) :
-- imply
  (p + q) n = p n + q n := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.laurentPoly_add_coeff p q n

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_laurentPoly_zero_coeff
  [CommRing K]
-- given
  (n : ℤ) :
-- imply
  (0 : LaurentPoly K) n = 0 := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.laurentPoly_zero_coeff n

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_laurentPoly_support_finite
  [CommRing K]
-- given
  (p : LaurentPoly K) :
-- imply
  {n : ℤ | p n ≠ 0}.Finite := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.laurentPoly_support_finite p

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_laurentPoly_support_eq
  [CommRing K]
-- given
  (p : LaurentPoly K) :
-- imply
  {n : ℤ | p n ≠ 0} = ↑p.support := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.laurentPoly_support_eq p

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_laurentPoly_ofFinsupp_coeff
  [CommRing K]
-- given
  (f : Finsupp ℤ K)
  (n : ℤ) :
-- imply
  laurentPoly_ofFinsupp f n = f n := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.laurentPoly_ofFinsupp_coeff f n

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_laurentPoly_single_coeff
  [CommRing K]
-- given
  (k : ℤ)
  (a : K)
  (n : ℤ) :
-- imply
  laurentPoly_single k a n = if n = k then a else 0 := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.laurentPoly_single_coeff k a n

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_laurentPoly_single_eq_C_mul_T
  [CommRing K]
-- given
  (k : ℤ)
  (a : K) :
-- imply
  laurentPoly_single k a = C a * T k := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.laurentPoly_single_eq_C_mul_T k a

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_laurentPoly_iff_essentiallyFinite
  [CommRing K]
-- given
  (f : ℤ → K) :
-- imply
  (∃ p : LaurentPoly K, ∀ n, p n = f n) ↔ {n : ℤ | f n ≠ 0}.Finite := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.laurentPoly_iff_essentiallyFinite f

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_T_isUnit
  [CommRing K] :
-- imply
  IsUnit (T 1 : LaurentPoly K) := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.T_isUnit

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_T_inv
  [CommRing K] :
-- imply
  (T 1 : LaurentPoly K) * T (-1) = 1 := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.T_inv

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_T_neg_one_mul_T
  [CommRing K] :
-- imply
  (T (-1) : LaurentPoly K) * T 1 = 1 := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.T_neg_one_mul_T

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_T_mul_coeff
  [CommRing K]
-- given
  (a : LaurentPoly K)
  (n : ℤ) :
-- imply
  (T 1 * a : LaurentPoly K) n = a (n - 1) := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.T_mul_coeff a n

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_T_neg_one_mul_coeff
  [CommRing K]
-- given
  (a : LaurentPoly K)
  (n : ℤ) :
-- imply
  (T (-1) * a : LaurentPoly K) n = a (n + 1) := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.T_neg_one_mul_coeff a n

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_mul_T_coeff
  [CommRing K]
-- given
  (a : LaurentPoly K)
  (n : ℤ) :
-- imply
  (a * T 1 : LaurentPoly K) n = a (n - 1) := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.mul_T_coeff a n

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_mul_T_neg_one_coeff
  [CommRing K]
-- given
  (a : LaurentPoly K)
  (n : ℤ) :
-- imply
  (a * T (-1) : LaurentPoly K) n = a (n + 1) := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.mul_T_neg_one_coeff a n

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_T_coeff_eq
  [CommRing K]
-- given
  (k i : ℤ) :
-- imply
  (T k : LaurentPoly K) i = if i = k then 1 else 0 := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.T_coeff_eq k i

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_T_eq_single
  [CommRing K]
-- given
  (k : ℤ) :
-- imply
  (T k : LaurentPoly K) = AddMonoidAlgebra.single k 1 := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.T_eq_single k

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_T_mul_T
  [CommRing K]
-- given
  (m n : ℤ) :
-- imply
  (T m : LaurentPoly K) * T n = T (m + n) := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.T_mul_T m n

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_T_one_pow
  [CommRing K]
-- given
  (n : ℕ) :
-- imply
  (T 1 : LaurentPoly K) ^ n = T n := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.T_one_pow n

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_T_one_zpow
  [CommRing K]
-- given
  (k : ℤ) :
-- imply
  (↑((isUnit_T (R := K) 1).unit ^ k) : LaurentPoly K) = T k := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.T_one_zpow k

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_T_one_zpow_coeff
  [CommRing K]
-- given
  (k i : ℤ) :
-- imply
  ((isUnit_T (R := K) 1).unit ^ k : (LaurentPoly K)ˣ).val i = if i = k then 1 else 0 := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.T_one_zpow_coeff k i

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_eq_sum_T
  [CommRing K]
-- given
  (a : LaurentPoly K) :
-- imply
  a = a.support.sum fun i => C (a i) * T i := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.eq_sum_T a

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_eq_sum_single
  [CommRing K]
-- given
  (a : LaurentPoly K) :
-- imply
  a = a.support.sum fun i => AddMonoidAlgebra.single i (a i) := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.eq_sum_single a

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_LaurentSeries_X_isUnit
  [CommRing K] :
-- imply
  IsUnit (HahnSeries.single (1 : ℤ) (1 : K)) := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.LaurentSeries_X_isUnit

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_laurentSeries_eq_hsum_single
  [CommRing K]
-- given
  (x : LaurentSeries K) :
-- imply
  x = (singleFamily x).hsum := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.laurentSeries_eq_hsum_single x

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_laurentSeries_coeff_eq_finsum_single
  [CommRing K]
-- given
  (x : LaurentSeries K)
  (n : ℤ) :
-- imply
  x.coeff n = finsum (fun i : x.support => (single (i : ℤ) (x.coeff i)).coeff n) := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.laurentSeries_coeff_eq_finsum_single x n

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_order_mul_ge
  [CommRing K]
-- given
  (f g : LaurentSeries K) :
-- imply
  f.orderTop + g.orderTop ≤ (f * g).orderTop := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.order_mul_ge f g

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_coeff_mul_eq_zero_of_lt_order
  [CommRing K]
-- given
  (f g : LaurentSeries K)
  (n : ℤ)
  (hn : n < f.order + g.order)
  (hf : f ≠ 0)
  (hg : g ≠ 0) :
-- imply
  (f * g).coeff n = 0 := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.coeff_mul_eq_zero_of_lt_order f g n hn hf hg

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_powerSeriesToLaurent_injective
  [CommRing K] :
-- imply
  Function.Injective (powerSeriesToLaurent (K := K)) := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.powerSeriesToLaurent_injective

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_coeff_powerSeriesToLaurent
  [CommRing K]
-- given
  (f : PowerSeries K)
  (n : ℕ) :
-- imply
  (powerSeriesToLaurent f).coeff n = PowerSeries.coeff n f := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.coeff_powerSeriesToLaurent f n

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_laurentPolynomialToSeries_add
  [CommRing K]
-- given
  (p q : LaurentPoly K) :
-- imply
  laurentPolynomialToSeries (p + q) = laurentPolynomialToSeries p + laurentPolynomialToSeries q := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.laurentPolynomialToSeries_add p q

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_laurentPolynomialToSeries_zero
  [CommRing K] :
-- imply
  laurentPolynomialToSeries (0 : LaurentPoly K) = 0 := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.laurentPolynomialToSeries_zero

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_laurentPolynomialToSeries_one
  [CommRing K] :
-- imply
  laurentPolynomialToSeries (1 : LaurentPoly K) = 1 := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.laurentPolynomialToSeries_one

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_laurentPolynomialToSeries_mul
  [CommRing K]
-- given
  (p q : LaurentPoly K) :
-- imply
  laurentPolynomialToSeries (p * q) = laurentPolynomialToSeries p * laurentPolynomialToSeries q := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.laurentPolynomialToSeries_mul p q

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_laurentPolynomialToSeries_coeff
  [CommRing K]
-- given
  (p : LaurentPoly K)
  (n : ℤ) :
-- imply
  (laurentPolynomialToSeries p).coeff n = p n := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.laurentPolynomialToSeries_coeff p n

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_exists_binaryRepresentation
-- given
  (n : ℕ) :
-- imply
  ∃ s : Finset ℕ, BinaryRepresentation n s := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.exists_binaryRepresentation n

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_binaryRepresentation_unique
  {n : ℕ}
  {s t : Finset ℕ}
-- given
  (hs : BinaryRepresentation n s)
  (ht : BinaryRepresentation n t) :
-- imply
  s = t := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.binaryRepresentation_unique hs ht

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_binaryRepresentation_exists_unique
-- given
  (n : ℕ) :
-- imply
  ∃! s : Finset ℕ, BinaryRepresentation n s := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.binaryRepresentation_exists_unique n

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_canonicalBinaryRep_spec
-- given
  (n : ℕ) :
-- imply
  BinaryRepresentation n (canonicalBinaryRep n) := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.canonicalBinaryRep_spec n

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_canonicalBinaryRep_eq_of_binaryRepresentation
  {n : ℕ}
  {s : Finset ℕ}
-- given
  (hs : BinaryRepresentation n s) :
-- imply
  s = canonicalBinaryRep n := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.canonicalBinaryRep_eq_of_binaryRepresentation hs

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_binaryRepEquiv_apply
-- given
  (n : ℕ) :
-- imply
  binaryRepEquiv n = canonicalBinaryRep n := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.binaryRepEquiv_apply n

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_binaryRepEquiv_symm_apply
-- given
  (s : Finset ℕ) :
-- imply
  binaryRepEquiv.symm s = ∑ i ∈ s, 2 ^ i := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.binaryRepEquiv_symm_apply s

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_binaryRepEquiv_left_inv
-- given
  (n : ℕ) :
-- imply
  binaryRepEquiv.symm (binaryRepEquiv n) = n := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.binaryRepEquiv_left_inv n

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_binaryRepEquiv_right_inv
-- given
  (s : Finset ℕ) :
-- imply
  binaryRepEquiv (binaryRepEquiv.symm s) = s := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.binaryRepEquiv_right_inv s

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_btDigits_card :
-- imply
  btDigits.card = 3 := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.btDigits_card

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_mem_btDigits_iff
-- given
  (b : ℤ) :
-- imply
  b ∈ btDigits ↔ b = -1 ∨ b = 0 ∨ b = 1 := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.mem_btDigits_iff b

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_card_kBoundedBTReps
-- given
  (k : ℕ) :
-- imply
  (kBoundedBTReps k).card = 3 ^ (k + 1) := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.card_kBoundedBTReps k

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_maxBT_eq
-- given
  (k : ℕ) :
-- imply
  2 * maxBT k + 1 = 3 ^ (k + 1) := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.maxBT_eq k

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_card_Icc_symm
-- given
  (M : ℕ) :
-- imply
  (Icc_symm M).card = 2 * M + 1 := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.card_Icc_symm M

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_card_Icc_symm_maxBT
-- given
  (k : ℕ) :
-- imply
  (Icc_symm (maxBT k)).card = 3 ^ (k + 1) := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.card_Icc_symm_maxBT k

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_sum_pow_three_Fin_eq_range
-- given
  (k : ℕ) :
-- imply
  (∑ i : Fin (k + 1), (3 : ℤ) ^ (i : ℕ)) = ∑ i ∈ Finset.range (k + 1), (3 : ℤ) ^ i := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.sum_pow_three_Fin_eq_range k

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_kBoundedBTValue_mem_Icc
-- given
  (k : ℕ)
  (f : Fin (k + 1) → ℤ)
  (hf : f ∈ kBoundedBTReps k) :
-- imply
  kBoundedBTValue k f ∈ Icc_symm (maxBT k) := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.kBoundedBTValue_mem_Icc k f hf

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_kBoundedBTValue_injective_on
-- given
  (k : ℕ) :
-- imply
  Set.InjOn (kBoundedBTValue k) (kBoundedBTReps k : Set (Fin (k + 1) → ℤ)) := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.kBoundedBTValue_injective_on k

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_kBounded_unique
-- given
  (k : ℕ)
  (n : ℤ)
  (hn : n ∈ Icc_symm (maxBT k)) :
-- imply
  ∃! f ∈ kBoundedBTReps k, kBoundedBTValue k f = n := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.kBounded_unique k n hn

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_kBoundedToFinsupp_apply
-- given
  (k i : ℕ)
  (hi : i < k + 1)
  (f : Fin (k + 1) → ℤ) :
-- imply
  kBoundedToFinsupp k f i = f ⟨i, hi⟩ := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.kBoundedToFinsupp_apply k f i hi

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_kBoundedToFinsupp_apply_of_ge
-- given
  (k i : ℕ)
  (hi : k + 1 ≤ i)
  (f : Fin (k + 1) → ℤ) :
-- imply
  kBoundedToFinsupp k f i = 0 := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.kBoundedToFinsupp_apply_of_ge k f i hi

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_kBoundedToFinsupp_sum
-- given
  (k : ℕ)
  (f : Fin (k + 1) → ℤ) :
-- imply
  ∑ i ∈ (kBoundedToFinsupp k f).support, (kBoundedToFinsupp k f) i * (3 : ℤ) ^ i = kBoundedBTValue k f := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.kBoundedToFinsupp_sum k f

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_balancedTernary_exists
-- given
  (n : ℤ) :
-- imply
  Nonempty (BalancedTernaryRep n) := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.balancedTernary_exists n

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_two_sum_lt_pow_three
-- given
  (k : ℕ) :
-- imply
  2 * ∑ i ∈ Finset.range k, (3 : ℤ) ^ i < 3 ^ k := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.two_sum_lt_pow_three k

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_sum_eq_sum_support'
-- given
  (f : Finsupp ℕ ℤ)
  (s : Finset ℕ)
  (hs : f.support ⊆ s) :
-- imply
  ∑ i ∈ s, f i * (3 : ℤ) ^ i = ∑ i ∈ f.support, f i * (3 : ℤ) ^ i := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.sum_eq_sum_support' f s hs

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_btDigits_diff_abs_ge_one
  {a b : ℤ}
-- given
  (ha : a ∈ btDigits)
  (hb : b ∈ btDigits)
  (hab : a ≠ b) :
-- imply
  |a - b| ≥ 1 := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.btDigits_diff_abs_ge_one ha hb hab

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_btDigits_diff_abs_le_two
  {a b : ℤ}
-- given
  (ha : a ∈ btDigits)
  (hb : b ∈ btDigits) :
-- imply
  |a - b| ≤ 2 := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.btDigits_diff_abs_le_two ha hb

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_btDigits_sum_unique
-- given
  (f g : Finsupp ℕ ℤ)
  (hf : ∀ i, f i ∈ btDigits)
  (hg : ∀ i, g i ∈ btDigits)
  (hsum : ∑ i ∈ f.support, f i * (3 : ℤ) ^ i = ∑ i ∈ g.support, g i * (3 : ℤ) ^ i) :
-- imply
  f = g := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.btDigits_sum_unique f g hf hg hsum

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_balancedTernary_unique
-- given
  (n : ℤ)
  (r1 r2 : BalancedTernaryRep n) :
-- imply
  r1.digits = r2.digits := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.balancedTernary_unique n r1 r2

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_balancedTernary_exists_unique
-- given
  (n : ℤ) :
-- imply
  ∃! f : Finsupp ℕ ℤ, (∀ i, f i ∈ btDigits) ∧ balancedTernaryValue f = n := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.balancedTernary_exists_unique n

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma toInt_mem_btDigits
-- given
  (d : BTDigit) :
-- imply
  d.toInt ∈ btDigits := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.BTDigit.toInt_mem_btDigits d

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma btDigitOfInt_toInt
-- given
  (z : ℤ)
  (hz : z ∈ btDigits) :
-- imply
  (btDigitOfInt z).toInt = z := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.btDigitOfInt_toInt z hz

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_toInt_btDigitOfInt
-- given
  (d : BTDigit) :
-- imply
  btDigitOfInt d.toInt = d := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.toInt_btDigitOfInt d

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma btDigitOfInt_zero :
-- imply
  btDigitOfInt 0 = AlgebraicCombinatorics.BalancedTernaryDigit.zero := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.btDigitOfInt_zero

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma btDigitOfInt_ne_zero_iff
-- given
  (z : ℤ)
  (hz : z ∈ btDigits) :
-- imply
  btDigitOfInt z ≠ 0 ↔ z ≠ 0 := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.btDigitOfInt_ne_zero_iff z hz

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma toFinsupp_toInductive_digits
  {n : ℤ}
-- given
  (r : BTRep n) :
-- imply
  r.toFinsupp.toInductive.digits = r.digits := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.BTRep.toFinsupp_toInductive_digits r

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma toInductive_toFinsupp_digits
  {n : ℤ}
-- given
  (r : BalancedTernaryRep n) :
-- imply
  r.toInductive.toFinsupp.digits = r.digits := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.BalancedTernaryRep.toInductive_toFinsupp_digits r

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_balancedTernary_representations_equiv
-- given
  (n : ℤ) :
-- imply
  (∃ _ : BalancedTernaryRep n, True) ↔ (∃ _ : BTRep n, True) := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.balancedTernary_representations_equiv n

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_isUnit_T_one_unit_eq
  [CommRing K] :
-- imply
  (isUnit_T (R := K) 1).unit = ⟨T 1, T (-1), by rw [← T_add]; simp, by rw [← T_add]; simp⟩ := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.isUnit_T_one_unit_eq

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/LaurentSeries.lean)
-/
@[path]
private lemma pv_balanced_ternary_injective
-- given
  (k : ℕ)
  (f g : Fin (k + 1) → ℤ)
  (hf : ∀ i, f i = -1 ∨ f i = 0 ∨ f i = 1)
  (hg : ∀ i, g i = -1 ∨ g i = 0 ∨ g i = 1)
  (hfg : ∑ i : Fin (k + 1), f i * (3 : ℤ) ^ (i : ℕ) = ∑ i : Fin (k + 1), g i * (3 : ℤ) ^ (i : ℕ)) :
-- imply
  f = g := by
-- proof
  apply AlgebraicCombinatorics.FPS.Laurent.balanced_ternary_injective k f g hf hg hfg


-- created on 2026-10-23
