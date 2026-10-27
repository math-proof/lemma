import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.RingTheory.LaurentSeries.Part11
open AlgebraicCombinatorics
open AlgebraicCombinatorics.BinaryRepresentation


section
-- ac-theorems


open scoped LaurentPolynomial

noncomputable section

namespace AlgebraicCombinatorics

namespace BinaryRepresentation

lemma bitsFromList_support_finite (L : List ℕ) (hL : ∀ x ∈ L, x < 2) :
    {i | bitsFromList L hL i ≠ 0}.Finite := by
  apply Set.Finite.subset (Set.finite_lt_nat L.length)
  intro i hi
  simp only [Set.mem_ofPred_eq, bitsFromList, ne_eq] at hi ⊢
  by_contra h
  push Not at h
  simp only [dite_eq_right (not_lt.mpr h), not_true_eq_false] at hi

@[simp]
lemma bitsFromList_of_lt {L : List ℕ} {hL : ∀ x ∈ L, x < 2} {i : ℕ} (hi : i < L.length) :
    (bitsFromList L hL i : ℕ) = L[i] := by
  simp only [bitsFromList, hi, ↓reduceDIte]

@[simp]
lemma bitsFromList_of_ge {L : List ℕ} {hL : ∀ x ∈ L, x < 2} {i : ℕ} (hi : L.length ≤ i) :
    bitsFromList L hL i = 0 := by
  simp only [bitsFromList, not_lt.mpr hi, ↓reduceDIte]

lemma bitsFromList_sum_eq (L : List ℕ) (hL : ∀ x ∈ L, x < 2) :
    ∑ᶠ i, (bitsFromList L hL i : ℕ) * 2^i = Nat.ofDigits 2 L := by
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range L.length)]
  · -- Show sum over range equals ofDigits
    induction L with
    | nil => simp [Nat.ofDigits]
    | cons d L' ih =>
      have hL' : ∀ x ∈ L', x < 2 := fun x hx => hL x (List.mem_cons_of_mem d hx)
      simp only [List.length_cons, Finset.sum_range_succ']
      rw [Nat.ofDigits_cons]
      have h0 : (0 : ℕ) < (d :: L').length := List.length_pos_of_ne_nil (List.cons_ne_nil d L')
      simp only [bitsFromList_of_lt h0, List.getElem_cons_zero, pow_zero, mul_one]
      rw [add_comm]
      congr 1
      -- Transform the sum
      have h_eq : ∀ x ∈ Finset.range L'.length, (bitsFromList (d :: L') hL (x + 1) : ℕ) =
                  (bitsFromList L' hL' x : ℕ) := by
        intro i hi
        simp only [Finset.mem_range] at hi
        have h1 : i + 1 < (d :: L').length := by simp; omega
        have h2 : i < L'.length := hi
        simp only [bitsFromList_of_lt h1, bitsFromList_of_lt h2, List.getElem_cons_succ]
      calc ∑ x ∈ Finset.range L'.length, (bitsFromList (d :: L') hL (x + 1) : ℕ) * 2 ^ (x + 1)
          = ∑ x ∈ Finset.range L'.length, (bitsFromList L' hL' x : ℕ) * 2 ^ (x + 1) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [h_eq i hi]
        _ = ∑ x ∈ Finset.range L'.length, (bitsFromList L' hL' x : ℕ) * (2 * 2 ^ x) := by
            apply Finset.sum_congr rfl
            intro i _
            ring_nf
        _ = ∑ x ∈ Finset.range L'.length, 2 * ((bitsFromList L' hL' x : ℕ) * 2 ^ x) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
        _ = 2 * ∑ x ∈ Finset.range L'.length, (bitsFromList L' hL' x : ℕ) * 2 ^ x := by
            rw [Finset.mul_sum]
        _ = 2 * Nat.ofDigits 2 L' := by rw [ih hL']
  · -- Support is contained in range
    intro i hi
    simp only [Function.mem_support, ne_eq, bitsFromList] at hi
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    push Not at h
    simp only [dite_eq_right (not_lt.mpr h), Fin.val_zero, zero_mul, not_true_eq_false] at hi

end BinaryRepresentation

/-- Every natural number has a binary representation.
This is part of Theorem `thm.fps.laure.binary-rep-uniq`. -/
lemma binaryRepresentation_exists (n : ℕ) : Nonempty (BinaryRepresentation n) := by
  let L := Nat.digits 2 n
  have hL : ∀ x ∈ L, x < 2 := fun x hx => Nat.digits_lt_base (by norm_num : 1 < 2) hx
  refine ⟨⟨BinaryRepresentation.bitsFromList L hL,
          BinaryRepresentation.bitsFromList_support_finite L hL, ?_⟩⟩
  rw [BinaryRepresentation.bitsFromList_sum_eq, Nat.ofDigits_digits]

/-- If the sum is 0, all bits must be 0. -/
lemma bits_eq_zero_of_sum_eq_zero {r : BinaryRepresentation 0} (i : ℕ) : r.bits i = 0 := by
  by_contra h
  have hsum := r.sum_eq
  have hfin : {i : ℕ | (r.bits i : ℕ) * 2^i ≠ 0}.Finite :=
    r.finite_support.subset (support_mul_pow_subset r.bits)
  have hpos : (r.bits i : ℕ) * 2^i > 0 := by
    have hb : (r.bits i : ℕ) ≥ 1 := by
      simp only [Fin.ext_iff] at h
      omega
    positivity
  have hmem : i ∈ hfin.toFinset := by
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, ne_eq]
    omega
  have hsum_pos : ∑ j ∈ hfin.toFinset, (r.bits j : ℕ) * 2^j > 0 := by
    apply Finset.sum_pos'
    · intro j _
      positivity
    · exact ⟨i, hmem, hpos⟩
  rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset)] at hsum
  · omega
  · intro j hj
    simp only [Function.mem_support, ne_eq] at hj
    exact hfin.mem_toFinset.mpr hj

/-- The binary representation of a natural number is unique.
This is Theorem `thm.fps.laure.binary-rep-uniq`. -/
lemma binaryRepresentation_unique (n : ℕ) (r₁ r₂ : BinaryRepresentation n) :
    r₁.bits = r₂.bits := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    funext i
    cases i with
    | zero =>
      have h1 := bits_zero_eq_mod n r₁
      have h2 := bits_zero_eq_mod n r₂
      ext
      omega
    | succ i =>
      by_cases hn : n = 0
      · subst hn
        have h1 := bits_eq_zero_of_sum_eq_zero (i + 1) (r := r₁)
        have h2 := bits_eq_zero_of_sum_eq_zero (i + 1) (r := r₂)
        rw [h1, h2]
      · have hdiv : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by omega)
        have hih := ih (n / 2) hdiv r₁.shift r₂.shift
        have : r₁.shift.bits i = r₂.shift.bits i := by rw [hih]
        simp only [BinaryRepresentation.shift] at this
        exact this

namespace BalancedTernaryDigit

/-- Different digits have different integer values -/
lemma toInt_injective : Function.Injective toInt := by
  intro a b h
  cases a <;> cases b <;> simp [toInt] at h <;> rfl

/-- The range of toInt is {-1, 0, 1} -/
lemma toInt_range (d : BalancedTernaryDigit) : -1 ≤ d.toInt ∧ d.toInt ≤ 1 := by
  cases d <;> simp [toInt]

/-- Different digits have different residues mod 3 -/
lemma toInt_mod_three_injective :
    Function.Injective (fun d : BalancedTernaryDigit => d.toInt % 3) := by
  intro a b h
  cases a <;> cases b <;> simp [toInt] at h <;> native_decide

lemma eq_of_toInt_mod_three_eq (a b : BalancedTernaryDigit)
    (h : a.toInt % 3 = b.toInt % 3) : a = b :=
  toInt_mod_three_injective h

end BalancedTernaryDigit

lemma digitOfMod3_spec (n : ℤ) : (n - (digitOfMod3 n).toInt) % 3 = 0 := by
  unfold digitOfMod3
  split_ifs with h1 h2
  · simp [BalancedTernaryDigit.toInt, h1]
  · simp only [BalancedTernaryDigit.toInt]
    rcases h2 with h2a | h2b <;> omega
  · simp only [BalancedTernaryDigit.toInt]
    have : n % 3 = 2 ∨ n % 3 = -1 := by
      have hmod := Int.emod_lt_of_pos n (by norm_num : (3 : ℤ) > 0)
      have hmod' := Int.emod_nonneg n (by norm_num : (3 : ℤ) ≠ 0)
      omega
    omega

lemma abs_div_three_lt (n : ℤ) (hn : n ≠ 0) :
    |(n - (digitOfMod3 n).toInt) / 3| < |n| := by
  set d := digitOfMod3 n
  have hdiv : (n - d.toInt) % 3 = 0 := digitOfMod3_spec n
  have hd := BalancedTernaryDigit.toInt_range d
  have hdiv' : 3 ∣ (n - d.toInt) := Int.dvd_of_emod_eq_zero hdiv
  obtain ⟨q, hq⟩ := hdiv'
  have hq' : (n - d.toInt) / 3 = q := by rw [hq]; exact Int.mul_ediv_cancel_left q (by norm_num)
  rw [hq']
  have hn_eq : n = 3 * q + d.toInt := by omega
  by_cases hq0 : q = 0
  · simp [hq0] at hn_eq; simp [hq0]; omega
  · by_cases hqpos : q > 0
    · have h1 : 3 * q ≥ 3 := by omega
      have h2 : 3 * q + d.toInt ≥ 2 := by omega
      have h3' : 3 * q + d.toInt > 0 := by omega
      rw [abs_of_pos hqpos, hn_eq, abs_of_pos h3']; omega
    · push Not at hqpos
      have hqneg : q < 0 := by omega
      have h1 : 3 * q ≤ -3 := by omega
      have h2 : 3 * q + d.toInt ≤ -2 := by omega
      have h3' : 3 * q + d.toInt < 0 := by omega
      rw [abs_of_neg hqneg, hn_eq, abs_of_neg h3']; omega

lemma natAbs_of_nonneg_eq_toNat (m : ℤ) (hm : 0 ≤ m) : m.natAbs = m.toNat := by
  have h1 : (m.natAbs : ℤ) = m := Int.natAbs_of_nonneg hm
  have h2 : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hm
  omega

lemma natAbs_lt_of_abs_lt (m n : ℤ) (h : |m| < |n|) (hn0 : n ≠ 0) :
    m.natAbs < n.natAbs := by
  rw [← Int.natAbs_abs m, ← Int.natAbs_abs n]
  have hm_nn : 0 ≤ |m| := abs_nonneg m
  have hn_nn : 0 ≤ |n| := abs_nonneg n
  have hn_pos : 0 < |n| := abs_pos.mpr hn0
  rw [natAbs_of_nonneg_eq_toNat |m| hm_nn, natAbs_of_nonneg_eq_toNat |n| hn_nn]
  rw [Int.toNat_lt_toNat hn_pos]
  exact h

/-- Every integer has a balanced ternary representation.
This is part of Theorem `thm.fps.laure.balanced-tern-rep-uniq`. -/
lemma balancedTernaryRepresentation_exists (n : ℤ) :
    Nonempty (BalancedTernaryRepresentation n) := by
  induction hn : n.natAbs using Nat.strong_induction_on generalizing n with
  | _ k ih =>
    by_cases hn0 : n = 0
    · subst hn0; exact ⟨zeroRep⟩
    · set d := digitOfMod3 n with hd_def
      set m := (n - d.toInt) / 3 with hm_def
      have hdiv : (n - d.toInt) % 3 = 0 := digitOfMod3_spec n
      have hm_abs : |m| < |n| := abs_div_three_lt n hn0
      have hm_nat : m.natAbs < k := by
        rw [← hn]
        exact natAbs_lt_of_abs_lt m n hm_abs hn0
      have ih_m := ih m.natAbs hm_nat m rfl
      obtain ⟨r⟩ := ih_m
      have hn_eq : n = d.toInt + 3 * m := by
        have hdiv' : 3 ∣ (n - d.toInt) := Int.dvd_of_emod_eq_zero hdiv
        obtain ⟨q, hq⟩ := hdiv'
        have : m = q := by simp only [hm_def, hq]; exact Int.mul_ediv_cancel_left q (by norm_num)
        omega
      rw [hn_eq]
      exact ⟨prependDigit d r⟩

/-- Key lemma: if sum of c_i * 3^i = 0 where c_i ∈ {-2,...,2} and only finitely many nonzero,
then all c_i = 0. This is the core uniqueness argument for balanced ternary representations. -/
lemma sum_powers_of_three_eq_zero_aux (k : ℕ) (c : ℕ → ℤ)
    (hc : ∀ i ≤ k, -2 ≤ c i ∧ c i ≤ 2)
    (hzero : ∀ i > k, c i = 0)
    (hsum : ∑ i ∈ Finset.range (k + 1), c i * (3 : ℤ)^i = 0) :
    ∀ i, c i = 0 := by
  induction k generalizing c with
  | zero =>
    intro i
    cases i with
    | zero =>
      simp at hsum
      have hc0 := hc 0 (le_refl 0)
      omega
    | succ j =>
      exact hzero (j + 1) (by omega)
  | succ k' ih =>
    -- c 0 must be 0 mod 3, so c 0 ∈ {-2,-1,0,1,2} ∩ 3ℤ = {0}
    have hmod : (∑ i ∈ Finset.range (k' + 2), c i * (3 : ℤ)^i) % 3 = 0 := by
      rw [hsum]
      simp
    rw [Finset.sum_range_succ'] at hmod
    simp only [pow_zero, mul_one] at hmod
    have hrest : (∑ i ∈ Finset.range (k' + 1), c (i + 1) * (3 : ℤ)^(i + 1)) % 3 = 0 := by
      rw [Finset.sum_int_mod]
      have h1 : ∀ i ∈ Finset.range (k' + 1), c (i + 1) * (3 : ℤ)^(i + 1) % 3 = 0 := by
        intro i _
        simp only [pow_succ]
        have h3 : (3 : ℤ) ^ i * 3 % 3 = 0 := by simp
        rw [Int.mul_emod, h3, mul_zero, Int.zero_emod]
      rw [Finset.sum_eq_zero h1]
      simp
    rw [Int.add_emod, hrest, zero_add] at hmod
    have hc0 := hc 0 (by omega)
    have hc0_mod : c 0 % 3 = 0 := by
      rw [Int.emod_emod_of_dvd] at hmod
      · exact hmod
      · norm_num
    have hc0_zero : c 0 = 0 := by omega
    -- Factor out 3 from the remaining sum
    rw [Finset.sum_range_succ'] at hsum
    simp only [pow_zero, mul_one, hc0_zero] at hsum
    have hfactor : ∑ i ∈ Finset.range (k' + 1), c (i + 1) * (3 : ℤ)^(i + 1) =
                   3 * ∑ i ∈ Finset.range (k' + 1), c (i + 1) * (3 : ℤ)^i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hfactor] at hsum
    have hc_sum' : ∑ i ∈ Finset.range (k' + 1), c (i + 1) * (3 : ℤ)^i = 0 := by
      have h3ne : (3 : ℤ) ≠ 0 := by norm_num
      have : 3 * ∑ i ∈ Finset.range (k' + 1), c (i + 1) * (3 : ℤ)^i + 0 = 0 := hsum
      linarith [mul_eq_zero.mp (by linarith : 3 * ∑ i ∈ Finset.range (k' + 1), c (i + 1) * (3 : ℤ)^i = 0)]
    -- Apply IH to the shifted sequence c' i = c (i + 1)
    let c' : ℕ → ℤ := fun i => c (i + 1)
    have hc'_bound : ∀ i ≤ k', -2 ≤ c' i ∧ c' i ≤ 2 := fun i hi => hc (i + 1) (by omega)
    have hc'_zero : ∀ i > k', c' i = 0 := fun i hi => hzero (i + 1) (by omega)
    have ih' := ih c' hc'_bound hc'_zero hc_sum'
    intro i
    cases i with
    | zero => exact hc0_zero
    | succ j => exact ih' j

/-- The balanced ternary representation of an integer is unique.
This is Theorem `thm.fps.laure.balanced-tern-rep-uniq`. -/
lemma balancedTernaryRepresentation_unique (n : ℤ)
    (r₁ r₂ : BalancedTernaryRepresentation n) : r₁.digits = r₂.digits := by
  -- Get bounds on the support
  obtain ⟨k₁, hk₁⟩ := r₁.finite_support.bddAbove
  obtain ⟨k₂, hk₂⟩ := r₂.finite_support.bddAbove
  let k := max k₁ k₂
  -- Both are k-bounded
  have h₁ : ∀ i > k, r₁.digits i = 0 := by
    intro i hi
    by_contra hc
    have : i ≤ k₁ := hk₁ hc
    omega
  have h₂ : ∀ i > k, r₂.digits i = 0 := by
    intro i hi
    by_contra hc
    have : i ≤ k₂ := hk₂ hc
    omega
  -- Convert finsum to finite sum
  have sum₁ : n = ∑ i ∈ Finset.range (k + 1), (r₁.digits i).toInt * (3 : ℤ)^i := by
    conv_lhs => rw [← r₁.sum_eq]
    apply finsum_eq_sum_of_support_subset
    intro i hi
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hc
    push Not at hc
    have hd : r₁.digits i = 0 := h₁ i hc
    change (r₁.digits i).toInt * (3 : ℤ)^i ≠ 0 at hi
    rw [hd, BalancedTernaryDigit.toInt_zero, zero_mul] at hi
    exact hi rfl
  have sum₂ : n = ∑ i ∈ Finset.range (k + 1), (r₂.digits i).toInt * (3 : ℤ)^i := by
    conv_lhs => rw [← r₂.sum_eq]
    apply finsum_eq_sum_of_support_subset
    intro i hi
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hc
    push Not at hc
    have hd : r₂.digits i = 0 := h₂ i hc
    change (r₂.digits i).toInt * (3 : ℤ)^i ≠ 0 at hi
    rw [hd, BalancedTernaryDigit.toInt_zero, zero_mul] at hi
    exact hi rfl
  -- Define the difference
  let c : ℕ → ℤ := fun i => (r₁.digits i).toInt - (r₂.digits i).toInt
  have hc_bound : ∀ i ≤ k, -2 ≤ c i ∧ c i ≤ 2 := by
    intro i _
    have h1 := BalancedTernaryDigit.toInt_range (r₁.digits i)
    have h2 := BalancedTernaryDigit.toInt_range (r₂.digits i)
    simp only [c]
    constructor <;> omega
  have hc_zero : ∀ i > k, c i = 0 := by
    intro i hi
    simp only [c]
    rw [h₁ i hi, h₂ i hi]
    simp
  have hc_sum : ∑ i ∈ Finset.range (k + 1), c i * (3 : ℤ)^i = 0 := by
    simp only [c]
    have : ∑ i ∈ Finset.range (k + 1), ((r₁.digits i).toInt - (r₂.digits i).toInt) * (3 : ℤ)^i =
           ∑ i ∈ Finset.range (k + 1), (r₁.digits i).toInt * (3 : ℤ)^i -
           ∑ i ∈ Finset.range (k + 1), (r₂.digits i).toInt * (3 : ℤ)^i := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [this, ← sum₁, ← sum₂]
    ring
  -- Apply the key lemma
  have hall := sum_powers_of_three_eq_zero_aux k c hc_bound hc_zero hc_sum
  -- Conclude that all digits are equal
  ext i
  have hi := hall i
  simp only [c] at hi
  have hr1 := BalancedTernaryDigit.toInt_range (r₁.digits i)
  have hr2 := BalancedTernaryDigit.toInt_range (r₂.digits i)
  apply BalancedTernaryDigit.toInt_injective
  omega

namespace DoublyInfinitePowerSeries

variable {K : Type*} [Semiring K]


@[simp]
lemma coeff_smul (r : K) (f : DoublyInfinitePowerSeries K) (n : ℤ) :
    coeff (r • f) n = r * coeff f n := rfl

@[simp]
lemma coeff_single (n m : ℤ) : coeff (single n : DoublyInfinitePowerSeries K) m =
    if m = n then 1 else 0 := rfl
@[simp]
lemma coeff_add (f g : DoublyInfinitePowerSeries K) (n : ℤ) :
    coeff (f + g) n = coeff f n + coeff g n := rfl

/-- The zero element of K[[x^±]] has all coefficients zero.
This is part of Definition `def.fps.laure.double`. -/
@[simp]
lemma coeff_zero (n : ℤ) : coeff (0 : DoublyInfinitePowerSeries K) n = 0 := rfl

/-- The single at 0 with coefficient 1 represents 1 (as a constant series). -/
@[simp]
lemma single_zero_eq_one : (single 0 : DoublyInfinitePowerSeries K) = fun n => if n = 0 then 1 else 0 := rfl

/-- Coefficient of single n at n is 1. -/
@[simp]
lemma coeff_single_self (n : ℤ) : coeff (single n : DoublyInfinitePowerSeries K) n = 1 := by
  simp [coeff_single]

/-- Coefficient of single n at m ≠ n is 0. -/
@[simp]
lemma coeff_single_ne {n m : ℤ} (h : m ≠ n) :
    coeff (single n : DoublyInfinitePowerSeries K) m = 0 := by
  simp [coeff_single, h]

/-- Scalar multiplication of single. -/
@[simp]
lemma smul_single (r : K) (n : ℤ) :
    r • (single n : DoublyInfinitePowerSeries K) = fun m => if m = n then r else 0 := by
  funext m
  show r * (if m = n then 1 else 0) = if m = n then r else 0
  split_ifs with h
  · simp
  · simp

/-- Any doubly infinite power series f equals (coeff f n) at position n.
This is the pointwise characterization of the notation ∑_{n∈ℤ} a_n x^n:
at each position m, the coefficient is a_m.

This formalizes the representation mentioned at the end of Definition `def.fps.laure.double`:
"we will later use the notation ∑_{n∈ℤ} a_n x^n for a family (a_n)_{n∈ℤ}".

Note: This is a formal identity of families. The "sum" is well-defined because
at each coefficient position m, only the term n = m contributes. -/
lemma eq_coeff_at_position (f : DoublyInfinitePowerSeries K) (m : ℤ) :
    f m = coeff f m := rfl

/-- The representation f = ∑_{n∈ℤ} (coeff f n) · x^n holds pointwise:
at position m, f m = (coeff f m) · 1 + ∑_{n≠m} (coeff f n) · 0 = coeff f m. -/
lemma coeff_eq_single_contrib (f : DoublyInfinitePowerSeries K) (m : ℤ) :
    coeff f m = coeff f m * coeff (single m : DoublyInfinitePowerSeries K) m := by
  simp

/-- The support of a Laurent series is bounded below. -/
lemma IsLaurentSeries.support_bddBelow {f : DoublyInfinitePowerSeries K}
    (hf : IsLaurentSeries f) : BddBelow {n : ℤ | coeff f n ≠ 0} := by
  obtain ⟨N, hN⟩ := hf
  use N
  intro n hn
  by_contra h
  push Not at h
  exact hn (hN n h)

/-- A Mathlib LaurentSeries satisfies our IsLaurentSeries predicate.

This shows that Mathlib's definition of LaurentSeries (as HahnSeries ℤ K)
matches the textbook Definition `def.fps.laure.lauser`. -/
lemma isLaurentSeries_ofLaurentSeries (f : LaurentSeries K) :
    IsLaurentSeries (ofLaurentSeries f) := by
  have h := f.isPWO_support
  by_cases hne : f.support.Nonempty
  · have hmin := h.isWF.min_mem hne
    use h.isWF.min hne
    intro n hn
    unfold ofLaurentSeries coeff
    by_contra h'
    have hmem : n ∈ f.support := by
      simp only [HahnSeries.mem_support]
      exact h'
    exact not_lt.mpr (h.isWF.min_le hne hmem) hn
  · use 0
    intro n _
    unfold ofLaurentSeries coeff
    simp only [Set.not_nonempty_iff_eq_empty, HahnSeries.support_eq_empty_iff] at hne
    simp only [hne, HahnSeries.coeff_zero]

/-- The round-trip from LaurentSeries to DoublyInfinitePowerSeries and back gives the same series -/
lemma toLaurentSeries_ofLaurentSeries (f : LaurentSeries K) :
    toLaurentSeries (ofLaurentSeries f) (isLaurentSeries_ofLaurentSeries f) = f := by
  ext n
  rfl

/-- The round-trip from DoublyInfinitePowerSeries to LaurentSeries and back gives the same function -/
lemma ofLaurentSeries_toLaurentSeries (f : DoublyInfinitePowerSeries K)
    (hf : IsLaurentSeries f) :
    ofLaurentSeries (toLaurentSeries f hf) = f := by
  funext n
  rfl

end DoublyInfinitePowerSeries


section LaurentPolynomials

variable (K : Type*) [CommSemiring K]


/-- The unity of K[x^±] is T 0 = (δ_{i,0})_{i∈ℤ}.
This is part of Theorem `thm.fps.laure.laupol-ring`. -/
lemma laurentPolynomial_one_eq_T_zero : (1 : K[T;T⁻¹]) = LaurentPolynomial.T 0 := rfl

/-- The unity of K[x^±] evaluated at index n is 1 if n = 0, else 0.
This is the explicit characterization from Theorem `thm.fps.laure.laupol-ring`. -/
@[simp]
lemma laurentPolynomial_one_apply (n : ℤ) :
    (1 : K[T;T⁻¹]).coeff n = if n = 0 then 1 else 0 := by
  simp only [laurentPolynomial_one_eq_T_zero K, LaurentPolynomial.T_apply]
  simp only [eq_comm]


/-- The element T 1 (corresponding to x) is invertible in K[T;T⁻¹].
This is part of Theorem `thm.fps.laure.laupol-ring`. -/
lemma laurentPolynomial_T_isUnit : IsUnit (LaurentPolynomial.T 1 : K[T;T⁻¹]) :=
  LaurentPolynomial.isUnit_T 1

/-- More generally, T n is invertible for any n ∈ ℤ.
This generalizes the invertibility statement in Theorem `thm.fps.laure.laupol-ring`. -/
lemma laurentPolynomial_T_isUnit' (n : ℤ) : IsUnit (LaurentPolynomial.T n : K[T;T⁻¹]) :=
  LaurentPolynomial.isUnit_T n


/-- Any Laurent polynomial f = (a_i)_{i ∈ ℤ} satisfies f = ∑_{i ∈ support f} a_i T^i.
This is Proposition `prop.fps.laure.a=sumaixi`.

Here we state this for Laurent polynomials, where the sum is finite. -/
lemma laurentPolynomial_eq_sum (f : K[T;T⁻¹]) :
    f = f.coeff.sum fun n a => LaurentPolynomial.C a * LaurentPolynomial.T n := by
  conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single f]
  congr 1
  ext n a
  simp [LaurentPolynomial.single_eq_C_mul_T]


/-- K[x^±] is isomorphic to the group algebra K[ℤ].
This is one of the alternative characterizations mentioned after Theorem `thm.fps.laure.laupol-ring`. -/
lemma laurentPolynomial_eq_groupAlgebra :
    K[T;T⁻¹] = AddMonoidAlgebra K ℤ := rfl

end LaurentPolynomials

section LaurentPolynomialsCommRing


end LaurentPolynomialsCommRing


section LaurentSeriesSection

variable (K : Type*) [CommRing K]

/-- The Laurent polynomial to series map sends single n r to single n r. -/
lemma laurentPolyToSeries_single (n : ℤ) (r : K) :
    laurentPolyToSeries K (AddMonoidAlgebra.single n r) = HahnSeries.single n r := by
  unfold laurentPolyToSeries
  simp only [AddMonoidAlgebra.liftNCRingHom_single]
  simp only [singleMonoidHom, MonoidHom.coe_mk, OneHom.coe_mk, HahnSeries.C]
  change HahnSeries.single 0 r * HahnSeries.single n 1 = HahnSeries.single n r
  rw [HahnSeries.single_mul_single]
  simp only [zero_add, mul_one]

/-- The Laurent polynomial to series map preserves coefficients. -/
lemma laurentPolyToSeries_coeff (f : K[T;T⁻¹]) (n : ℤ) :
    (laurentPolyToSeries K f).coeff n = f.coeff n := by
  conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single f]
  rw [Finsupp.sum, map_sum]
  rw [HahnSeries.coeff_sum]
  simp_rw [laurentPolyToSeries_single, HahnSeries.coeff_single]
  by_cases hn : n ∈ f.coeff.support
  · rw [Finset.sum_eq_single n]
    · simp
    · intro b _ hbn
      simp [hbn.symm]
    · intro h
      exact absurd hn h
  · rw [Finset.sum_eq_zero]
    · simp only [Finsupp.mem_support_iff, ne_eq, not_not] at hn
      exact hn.symm
    · intro x hx
      simp only [Finsupp.mem_support_iff, ne_eq] at hn hx
      by_cases hxn : n = x
      · subst hxn
        exact absurd hx hn
      · simp [hxn]

/-- The Laurent polynomial to series map is injective. -/
lemma laurentPolyToSeries_injective : Function.Injective (laurentPolyToSeries K) := by
  intro f g hfg
  ext n
  rw [← laurentPolyToSeries_coeff K f n, ← laurentPolyToSeries_coeff K g n, hfg]

/-- The Laurent polynomial ring K[x^±] can be embedded into the Laurent series ring K((x)).
This is mentioned after Theorem `thm.fps.laure.lauser-ring`. -/
lemma laurentPolynomial_embeds_in_laurentSeries :
    ∃ (f : K[T;T⁻¹] →+* LaurentSeries K), Function.Injective f :=
  ⟨laurentPolyToSeries K, laurentPolyToSeries_injective K⟩

/-- For any positive integer i, the power series 1 - x^i is invertible in K[[x]]
and hence also in K((x)). This allows the computation in the proof of
Theorem `thm.fps.laure.balanced-tern-rep-uniq`. -/
lemma one_sub_X_pow_isUnit (i : ℕ) (hi : 0 < i) :
    IsUnit (1 - (PowerSeries.X : PowerSeries K)^i) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  simp only [map_sub, map_one, map_pow, PowerSeries.constantCoeff_X,
    zero_pow (Nat.ne_of_gt hi), sub_zero, isUnit_one]

end LaurentSeriesSection


section ModuleStructure

variable {K : Type*} [CommRing K] [Nontrivial K]

/-- The multiplication (1-x) · (∑_{n ∈ ℤ} x^n) = 0 shows that K[[x^±]] has torsion
as a K[x^±]-module. This is the calculation showing why we cannot divide by (1-x)
in K[[x^±]].

This corresponds to the discussion at the end of the section. -/
lemma torsion_example :
    ∃ (p : K[T;T⁻¹]) (f : DoublyInfinitePowerSeries K),
      p ≠ 0 ∧ f ≠ 0 ∧ laurentPolynomialSmul p f = 0 := by
  -- p = 1 - T 1 = 1 - x
  -- f = fun _ => 1 (the constant 1 function, representing ∑_{n ∈ ℤ} x^n)
  use 1 - LaurentPolynomial.T 1
  use fun _ => 1
  refine ⟨?_, ?_, ?_⟩
  · -- Show p ≠ 0
    intro h
    have h0 : ((1 : K[T;T⁻¹]) - (LaurentPolynomial.T 1 : K[T;T⁻¹])).coeff 0 = 0 := by
      rw [h]
      simp
    have hval : ((1 : K[T;T⁻¹]) - (LaurentPolynomial.T 1 : K[T;T⁻¹])).coeff 0 = 1 := by
      rw [laurentPolynomial_one_eq_T_zero K, AddMonoidAlgebra.coeff_sub]
      simp [Finsupp.sub_apply, LaurentPolynomial.T_apply]
    rw [hval] at h0
    exact one_ne_zero h0
  · -- Show f ≠ 0
    intro h
    have : (fun _ : ℤ => (1 : K)) 0 = 0 := by rw [h]; rfl
    exact one_ne_zero this
  · -- Show laurentPolynomialSmul p f = 0
    funext n
    simp only [laurentPolynomialSmul]
    -- The result is (0 : DoublyInfinitePowerSeries K) n = 0
    show (1 - LaurentPolynomial.T 1 : K[T;T⁻¹]).coeff.sum (fun i b => b * (1 : K)) = (0 : K)
    -- Need to compute the sum
    simp only [mul_one]
    have hcoeff : (1 - LaurentPolynomial.T 1 : K[T;T⁻¹]).coeff =
        (Finsupp.single 0 (1 : K) - Finsupp.single 1 1 : ℤ →₀ K) := rfl
    rw [hcoeff]
    -- (single 0 1 - single 1 1).sum (fun i b => b)
    rw [show (Finsupp.single 0 (1 : K) - Finsupp.single 1 1 : ℤ →₀ K).sum (fun _ b => b) =
        ∑ i ∈ (Finsupp.single 0 (1 : K) - Finsupp.single 1 1 : ℤ →₀ K).support,
          (Finsupp.single 0 (1 : K) - Finsupp.single 1 1 : ℤ →₀ K) i from rfl]
    -- The support is a subset of {0, 1}
    have hsup : (Finsupp.single 0 (1 : K) - Finsupp.single 1 1 : ℤ →₀ K).support ⊆ {0, 1} := by
      intro x hx
      simp only [Finsupp.mem_support_iff, ne_eq] at hx
      by_contra h
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h
      have hx0 : x ≠ 0 := h.1
      have hx1 : x ≠ 1 := h.2
      have : (Finsupp.single 0 (1 : K) - Finsupp.single 1 1 : ℤ →₀ K) x = 0 := by
        rw [Finsupp.sub_apply, Finsupp.single_apply, Finsupp.single_apply]
        rw [ite_eq_right (hx0.symm), ite_eq_right (hx1.symm)]
        ring
      exact hx this
    rw [Finset.sum_subset hsup]
    · -- Now compute the sum over {0, 1}
      have h0 : (Finsupp.single 0 (1 : K) - Finsupp.single 1 1 : ℤ →₀ K) 0 = 1 := by
        rw [Finsupp.sub_apply, Finsupp.single_apply, Finsupp.single_apply]
        norm_num
      have h1' : (Finsupp.single 0 (1 : K) - Finsupp.single 1 1 : ℤ →₀ K) 1 = -1 := by
        rw [Finsupp.sub_apply, Finsupp.single_apply, Finsupp.single_apply]
        norm_num
      simp only [Finset.sum_insert (by simp : (0 : ℤ) ∉ ({1} : Finset ℤ)),
                 Finset.sum_singleton, h0, h1']
      ring
    · intro x _ hx
      simp only [Finsupp.mem_support_iff, ne_eq, not_not] at hx
      exact hx

end ModuleStructure

/-- For k-bounded representations, the finsum equals a finite sum over range(k+1). -/
lemma bounded_sum_eq {n : ℤ} (r : BalancedTernaryRepresentation n) (k : ℕ)
    (hk : r.isBounded k) :
    n = ∑ i ∈ Finset.range (k + 1), (r.digits i).toInt * (3 : ℤ)^i := by
  have h := r.sum_eq
  conv_lhs => rw [← h]
  apply finsum_eq_sum_of_support_subset
  intro i hi
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hc
  push Not at hc
  have hd : r.digits i = 0 := hk i hc
  change (r.digits i).toInt * (3 : ℤ)^i ≠ 0 at hi
  rw [hd, BalancedTernaryDigit.toInt_zero, zero_mul] at hi
  exact hi rfl

/-- Key lemma: if sum of c_i * 3^i = 0 where c_i ∈ {-2,...,2}, then all c_i = 0.

This is the core uniqueness argument: the difference of two balanced ternary
representations has coefficients in {-2,...,2}, and if the sum is 0, all
coefficients must be 0. -/
lemma sum_powers_of_three_eq_zero (k : ℕ) (c : ℕ → ℤ)
    (hc : ∀ i ≤ k, -2 ≤ c i ∧ c i ≤ 2)
    (hzero : ∀ i > k, c i = 0)
    (hsum : ∑ i ∈ Finset.range (k + 1), c i * (3 : ℤ)^i = 0) :
    ∀ i, c i = 0 := by
  induction k generalizing c with
  | zero =>
    intro i
    cases i with
    | zero =>
      simp at hsum
      have hc0 := hc 0 (le_refl 0)
      omega
    | succ j =>
      exact hzero (j + 1) (by omega)
  | succ k ih =>
    -- The key: c 0 must be 0 mod 3, so c 0 ∈ {-2,-1,0,1,2} ∩ 3ℤ = {0}
    have hmod : (∑ i ∈ Finset.range (k + 2), c i * (3 : ℤ)^i) % 3 = 0 := by
      rw [hsum]
      simp
    rw [Finset.sum_range_succ'] at hmod
    simp only [pow_zero, mul_one] at hmod
    have hrest : (∑ i ∈ Finset.range (k + 1), c (i + 1) * (3 : ℤ)^(i + 1)) % 3 = 0 := by
      rw [Finset.sum_int_mod]
      have h1 : ∀ i ∈ Finset.range (k + 1), c (i + 1) * (3 : ℤ)^(i + 1) % 3 = 0 := by
        intro i _
        simp only [pow_succ]
        have h3 : (3 : ℤ) ^ i * 3 % 3 = 0 := by simp
        rw [Int.mul_emod, h3, mul_zero, Int.zero_emod]
      rw [Finset.sum_eq_zero h1]
      simp
    rw [Int.add_emod, hrest, zero_add] at hmod
    have hc0 := hc 0 (by omega)
    have hc0_mod : c 0 % 3 = 0 := by
      rw [Int.emod_emod_of_dvd] at hmod
      · exact hmod
      · norm_num
    have hc0_zero : c 0 = 0 := by omega
    -- Now we can factor out 3 from the remaining sum
    rw [Finset.sum_range_succ'] at hsum
    simp only [pow_zero, mul_one, hc0_zero] at hsum
    have hfactor : ∑ i ∈ Finset.range (k + 1), c (i + 1) * (3 : ℤ)^(i + 1) =
                   3 * ∑ i ∈ Finset.range (k + 1), c (i + 1) * (3 : ℤ)^i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hfactor] at hsum
    have hsum' : ∑ i ∈ Finset.range (k + 1), c (i + 1) * (3 : ℤ)^i = 0 := by
      simp at hsum
      exact hsum
    -- Apply IH to the shifted sequence c' i = c (i + 1)
    let c' : ℕ → ℤ := fun i => c (i + 1)
    have hc' : ∀ i ≤ k, -2 ≤ c' i ∧ c' i ≤ 2 := fun i hi => hc (i + 1) (by omega)
    have hzero' : ∀ i > k, c' i = 0 := fun i hi => hzero (i + 1) (by omega)
    have hsum'' : ∑ i ∈ Finset.range (k + 1), c' i * (3 : ℤ)^i = 0 := hsum'
    have ih' := ih c' hc' hzero' hsum''
    intro i
    cases i with
    | zero => exact hc0_zero
    | succ j => exact ih' j

/-- Each integer n with |n| ≤ 3^0 + 3^1 + ... + 3^k has a unique k-bounded
balanced ternary representation.

This is the key lemma used in the rigorous proof of
Theorem `thm.fps.laure.balanced-tern-rep-uniq`. -/
lemma balancedTernaryRepresentation_bounded_unique (k : ℕ) (n : ℤ)
    (_hn : |n| ≤ ∑ i ∈ Finset.range (k + 1), (3 : ℤ)^i)
    (r₁ r₂ : BalancedTernaryRepresentation n)
    (h₁ : r₁.isBounded k) (h₂ : r₂.isBounded k) :
    r₁.digits = r₂.digits := by
  -- Define the difference of digits
  let c : ℕ → ℤ := fun i => (r₁.digits i).toInt - (r₂.digits i).toInt
  -- Show c satisfies the conditions of sum_powers_of_three_eq_zero
  have hc : ∀ i ≤ k, -2 ≤ c i ∧ c i ≤ 2 := by
    intro i _
    have h1 := BalancedTernaryDigit.toInt_range (r₁.digits i)
    have h2 := BalancedTernaryDigit.toInt_range (r₂.digits i)
    simp only [c]
    constructor <;> omega
  have hzero : ∀ i > k, c i = 0 := by
    intro i hi
    simp only [c]
    rw [h₁ i hi, h₂ i hi]
    simp
  have hsum : ∑ i ∈ Finset.range (k + 1), c i * (3 : ℤ)^i = 0 := by
    have h1 := bounded_sum_eq r₁ k h₁
    have h2 := bounded_sum_eq r₂ k h₂
    simp only [c]
    have : ∑ i ∈ Finset.range (k + 1), ((r₁.digits i).toInt - (r₂.digits i).toInt) * (3 : ℤ)^i =
           ∑ i ∈ Finset.range (k + 1), (r₁.digits i).toInt * (3 : ℤ)^i -
           ∑ i ∈ Finset.range (k + 1), (r₂.digits i).toInt * (3 : ℤ)^i := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [this, ← h1, ← h2]
    ring
  -- Apply the key lemma
  have hall := sum_powers_of_three_eq_zero k c hc hzero hsum
  -- Conclude that all digits are equal
  ext i
  have hi := hall i
  simp only [c] at hi
  have hr1 := BalancedTernaryDigit.toInt_range (r₁.digits i)
  have hr2 := BalancedTernaryDigit.toInt_range (r₂.digits i)
  apply BalancedTernaryDigit.toInt_injective
  omega

/-- The identity 1 + x + x^{-1} = (1 - x^3) / (x(1-x)) as Laurent polynomials.
This is used in simplifying the partial products. -/
lemma one_plus_T_plus_Tinv_eq (K : Type*) [CommRing K] :
    (1 + LaurentPolynomial.T 1 + LaurentPolynomial.T (-1) : K[T;T⁻¹]) *
    (LaurentPolynomial.T 1 * (1 - LaurentPolynomial.T 1)) =
    (1 - LaurentPolynomial.T 3) := by
  simp only [mul_sub, mul_one, one_mul, add_mul, ← LaurentPolynomial.T_add]
  norm_num
  ring

/-- The sum 3^0 + 3^1 + ... + 3^k = (3^{k+1} - 1) / 2.
This is used in bounding the range of balanced ternary representations. -/
lemma geom_sum_three (k : ℕ) :
    2 * ∑ i ∈ Finset.range (k + 1), (3 : ℤ)^i = (3 : ℤ)^(k + 1) - 1 := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    ring_nf
    have : (∑ x ∈ Finset.range (1 + n), (3 : ℤ) ^ x) * 2 = 3 ^ (n + 1) - 1 := by
      simp only [add_comm 1 n]
      convert ih using 1
      ring
    omega

end AlgebraicCombinatorics
end


/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma binary_representation_exists_is
-- given
  (n : ℕ) :
-- imply
  Nonempty (AlgebraicCombinatorics.BinaryRepresentation n) := by
-- proof
  apply AlgebraicCombinatorics.binaryRepresentation_exists n

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma binary_representation_unique_eq
-- given
  (n : ℕ)
  (r₁ r₂ : AlgebraicCombinatorics.BinaryRepresentation n) :
-- imply
  r₁.bits = r₂.bits := by
-- proof
  apply AlgebraicCombinatorics.binaryRepresentation_unique n r₁ r₂

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma to_int_zero_eq :
-- imply
  (0 : AlgebraicCombinatorics.BalancedTernaryDigit).toInt = 0 := by
-- proof
  apply AlgebraicCombinatorics.BalancedTernaryDigit.toInt_zero

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma to_int_injective_is :
-- imply
  Function.Injective AlgebraicCombinatorics.BalancedTernaryDigit.toInt := by
-- proof
  apply AlgebraicCombinatorics.BalancedTernaryDigit.toInt_injective

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma to_int_range_le
-- given
  (d : AlgebraicCombinatorics.BalancedTernaryDigit) :
-- imply
  -1 ≤ d.toInt ∧ d.toInt ≤ 1 := by
-- proof
  apply AlgebraicCombinatorics.BalancedTernaryDigit.toInt_range d

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma to_int_mod_three_injective_is :
-- imply
  Function.Injective fun d : AlgebraicCombinatorics.BalancedTernaryDigit => d.toInt % 3 := by
-- proof
  apply AlgebraicCombinatorics.BalancedTernaryDigit.toInt_mod_three_injective

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma eq_of_to_int_mod_three_eq_eq
-- given
  (a b : AlgebraicCombinatorics.BalancedTernaryDigit)
  (h : a.toInt % 3 = b.toInt % 3) :
-- imply
  a = b := by
-- proof
  apply AlgebraicCombinatorics.BalancedTernaryDigit.eq_of_toInt_mod_three_eq a b h

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma ne_zero_iff_to_int_ne_zero_iff
-- given
  (d : AlgebraicCombinatorics.BalancedTernaryDigit) :
-- imply
  d ≠ 0 ↔ d.toInt ≠ 0 := by
-- proof
  apply AlgebraicCombinatorics.BalancedTernaryDigit.ne_zero_iff_toInt_ne_zero d

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma balanced_ternary_representation_exists_is
-- given
  (n : ℤ) :
-- imply
  Nonempty (AlgebraicCombinatorics.BalancedTernaryRepresentation n) := by
-- proof
  apply AlgebraicCombinatorics.balancedTernaryRepresentation_exists n

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma balanced_ternary_representation_unique_eq
-- given
  (n : ℤ)
  (r₁ r₂ : AlgebraicCombinatorics.BalancedTernaryRepresentation n) :
-- imply
  r₁.digits = r₂.digits := by
-- proof
  apply AlgebraicCombinatorics.balancedTernaryRepresentation_unique n r₁ r₂

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma ext_eq
  [Semiring K]
-- given
  (f g : AlgebraicCombinatorics.DoublyInfinitePowerSeries K)
  (h : ∀ (n : ℤ), f.coeff n = g.coeff n) :
-- imply
  f = g := by
-- proof
  apply AlgebraicCombinatorics.DoublyInfinitePowerSeries.ext h

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma coeff_add_eq
  [Semiring K]
-- given
  (f g : AlgebraicCombinatorics.DoublyInfinitePowerSeries K)
  (n : ℤ) :
-- imply
  (f + g).coeff n = f.coeff n + g.coeff n := by
-- proof
  apply AlgebraicCombinatorics.DoublyInfinitePowerSeries.coeff_add f g n

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma coeff_smul_eq
  [Semiring K]
-- given
  (r : K)
  (f : AlgebraicCombinatorics.DoublyInfinitePowerSeries K)
  (n : ℤ) :
-- imply
  (r • f).coeff n = r * f.coeff n := by
-- proof
  apply AlgebraicCombinatorics.DoublyInfinitePowerSeries.coeff_smul r f n

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma coeff_single_eq
  [Semiring K]
-- given
  (n m : ℤ) :
-- imply
  (AlgebraicCombinatorics.DoublyInfinitePowerSeries.single n).coeff m =
    if m = n then 1 else 0 := by
-- proof
  apply AlgebraicCombinatorics.DoublyInfinitePowerSeries.coeff_single n m

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma coeff_zero_eq
  [Semiring K]
-- given
  (n : ℤ) :
-- imply
  (0 : AlgebraicCombinatorics.DoublyInfinitePowerSeries K).coeff n = 0 := by
-- proof
  apply AlgebraicCombinatorics.DoublyInfinitePowerSeries.coeff_zero n

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma single_zero_eq_one_eq
  [Semiring K] :
-- imply
  AlgebraicCombinatorics.DoublyInfinitePowerSeries.single 0 =
    fun n => if n = 0 then 1 else 0 := by
-- proof
  apply AlgebraicCombinatorics.DoublyInfinitePowerSeries.single_zero_eq_one

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma coeff_single_self_eq
  [Semiring K]
-- given
  (n : ℤ) :
-- imply
  (AlgebraicCombinatorics.DoublyInfinitePowerSeries.single n).coeff n = 1 := by
-- proof
  apply AlgebraicCombinatorics.DoublyInfinitePowerSeries.coeff_single_self n

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma coeff_single_ne_eq
  [Semiring K]
-- given
  (n m : ℤ)
  (h : m ≠ n) :
-- imply
  (AlgebraicCombinatorics.DoublyInfinitePowerSeries.single n).coeff m = 0 := by
-- proof
  apply AlgebraicCombinatorics.DoublyInfinitePowerSeries.coeff_single_ne h

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma smul_single_eq
  [Semiring K]
-- given
  (r : K)
  (n : ℤ) :
-- imply
  r • AlgebraicCombinatorics.DoublyInfinitePowerSeries.single n =
    fun m => if m = n then r else 0 := by
-- proof
  apply AlgebraicCombinatorics.DoublyInfinitePowerSeries.smul_single r n

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma eq_coeff_at_position_eq
  [Semiring K]
-- given
  (f : AlgebraicCombinatorics.DoublyInfinitePowerSeries K)
  (m : ℤ) :
-- imply
  f m = f.coeff m := by
-- proof
  apply AlgebraicCombinatorics.DoublyInfinitePowerSeries.eq_coeff_at_position f m

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma coeff_eq_single_contrib_eq
  [Semiring K]
-- given
  (f : AlgebraicCombinatorics.DoublyInfinitePowerSeries K)
  (m : ℤ) :
-- imply
  f.coeff m =
    f.coeff m * (AlgebraicCombinatorics.DoublyInfinitePowerSeries.single m).coeff m := by
-- proof
  apply AlgebraicCombinatorics.DoublyInfinitePowerSeries.coeff_eq_single_contrib f m

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma is_laurent_series_support_bdd_below_is
  [Semiring K]
-- given
  (f : AlgebraicCombinatorics.DoublyInfinitePowerSeries K)
  (hf : f.IsLaurentSeries) :
-- imply
  BddBelow {n : ℤ | f.coeff n ≠ 0} := by
-- proof
  apply AlgebraicCombinatorics.DoublyInfinitePowerSeries.IsLaurentSeries.support_bddBelow hf

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma is_laurent_series_of_laurent_series_is
  [Semiring K]
-- given
  (f : LaurentSeries K) :
-- imply
  (AlgebraicCombinatorics.DoublyInfinitePowerSeries.ofLaurentSeries f).IsLaurentSeries := by
-- proof
  apply AlgebraicCombinatorics.DoublyInfinitePowerSeries.isLaurentSeries_ofLaurentSeries f

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma int_is_pwo_of_bdd_below_is
-- given
  (s : Set ℤ)
  (hs : BddBelow s) :
-- imply
  s.IsPWO := by
-- proof
  apply AlgebraicCombinatorics.DoublyInfinitePowerSeries.Int.isPWO_of_bddBelow hs

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma to_laurent_series_of_laurent_series_eq
  [Semiring K]
-- given
  (f : LaurentSeries K) :
-- imply
  AlgebraicCombinatorics.DoublyInfinitePowerSeries.toLaurentSeries
    (AlgebraicCombinatorics.DoublyInfinitePowerSeries.ofLaurentSeries f)
    (AlgebraicCombinatorics.DoublyInfinitePowerSeries.isLaurentSeries_ofLaurentSeries f) = f := by
-- proof
  apply AlgebraicCombinatorics.DoublyInfinitePowerSeries.toLaurentSeries_ofLaurentSeries f

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma of_laurent_series_to_laurent_series_eq
  [Semiring K]
-- given
  (f : AlgebraicCombinatorics.DoublyInfinitePowerSeries K)
  (hf : f.IsLaurentSeries) :
-- imply
  AlgebraicCombinatorics.DoublyInfinitePowerSeries.ofLaurentSeries
    (AlgebraicCombinatorics.DoublyInfinitePowerSeries.toLaurentSeries f hf) = f := by
-- proof
  apply AlgebraicCombinatorics.DoublyInfinitePowerSeries.ofLaurentSeries_toLaurentSeries f hf

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma laurent_polynomial_one_eq_t_zero_eq
-- given
  (K : Type*)
  [CommSemiring K] :
-- imply
  (1 : LaurentPolynomial K) = LaurentPolynomial.T 0 := by
-- proof
  apply AlgebraicCombinatorics.laurentPolynomial_one_eq_T_zero K

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma laurent_polynomial_one_apply_eq
-- given
  (K : Type*)
  [CommSemiring K]
  (n : ℤ) :
-- imply
  (1 : LaurentPolynomial K).coeff n = if n = 0 then 1 else 0 := by
-- proof
  apply AlgebraicCombinatorics.laurentPolynomial_one_apply K n

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma laurent_polynomial_t_is_unit_is
-- given
  (K : Type*)
  [CommSemiring K] :
-- imply
  IsUnit (LaurentPolynomial.T 1 : LaurentPolynomial K) := by
-- proof
  apply AlgebraicCombinatorics.laurentPolynomial_T_isUnit K

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma laurent_polynomial_t_is_unit'_is
-- given
  (K : Type*)
  [CommSemiring K]
  (n : ℤ) :
-- imply
  IsUnit (LaurentPolynomial.T n : LaurentPolynomial K) := by
-- proof
  apply AlgebraicCombinatorics.laurentPolynomial_T_isUnit' K n

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma laurent_polynomial_t_mul_t_neg_eq
-- given
  (K : Type*)
  [CommSemiring K]
  (n : ℤ) :
-- imply
  (LaurentPolynomial.T n : LaurentPolynomial K) * LaurentPolynomial.T (-n) = 1 := by
-- proof
  apply AlgebraicCombinatorics.laurentPolynomial_T_mul_T_neg K n

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma laurent_polynomial_t_neg_mul_t_eq
-- given
  (K : Type*)
  [CommSemiring K]
  (n : ℤ) :
-- imply
  (LaurentPolynomial.T (-n) : LaurentPolynomial K) * LaurentPolynomial.T n = 1 := by
-- proof
  apply AlgebraicCombinatorics.laurentPolynomial_T_neg_mul_T K n

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma laurent_polynomial_eq_sum_eq
-- given
  (K : Type*)
  [CommSemiring K]
  (f : LaurentPolynomial K) :
-- imply
  f = f.coeff.sum fun n a => LaurentPolynomial.C a * LaurentPolynomial.T n := by
-- proof
  apply AlgebraicCombinatorics.laurentPolynomial_eq_sum K f

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma laurent_polynomial_eq_group_algebra_eq
-- given
  (K : Type*)
  [CommSemiring K] :
-- imply
  LaurentPolynomial K = AddMonoidAlgebra K ℤ := by
-- proof
  apply AlgebraicCombinatorics.laurentPolynomial_eq_groupAlgebra K

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma laurent_poly_to_series_single_eq
-- given
  (K : Type*)
  [CommRing K]
  (n : ℤ)
  (r : K) :
-- imply
  AlgebraicCombinatorics.laurentPolyToSeries K (AddMonoidAlgebra.single n r) =
    HahnSeries.single n r := by
-- proof
  apply AlgebraicCombinatorics.laurentPolyToSeries_single K n r

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma laurent_poly_to_series_coeff_eq
-- given
  (K : Type*)
  [CommRing K]
  (f : LaurentPolynomial K)
  (n : ℤ) :
-- imply
  (AlgebraicCombinatorics.laurentPolyToSeries K f).coeff n = f.coeff n := by
-- proof
  apply AlgebraicCombinatorics.laurentPolyToSeries_coeff K f n

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma laurent_poly_to_series_injective_is
-- given
  (K : Type*)
  [CommRing K] :
-- imply
  Function.Injective (AlgebraicCombinatorics.laurentPolyToSeries K) := by
-- proof
  apply AlgebraicCombinatorics.laurentPolyToSeries_injective K

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma laurent_polynomial_embeds_in_laurent_series_is
-- given
  (K : Type*)
  [CommRing K] :
-- imply
  ∃ f : LaurentPolynomial K →+* LaurentSeries K, Function.Injective f := by
-- proof
  apply AlgebraicCombinatorics.laurentPolynomial_embeds_in_laurentSeries K

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma one_sub_x_pow_is_unit_is
-- given
  (K : Type*)
  [CommRing K]
  (i : ℕ)
  (hi : 0 < i) :
-- imply
  IsUnit (1 - (PowerSeries.X : PowerSeries K) ^ i) := by
-- proof
  apply AlgebraicCombinatorics.one_sub_X_pow_isUnit K i hi

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma torsion_example_is
  [CommRing K] [Nontrivial K] :
-- imply
  ∃ (p : LaurentPolynomial K) (f : AlgebraicCombinatorics.DoublyInfinitePowerSeries K),
    p ≠ 0 ∧ f ≠ 0 ∧ AlgebraicCombinatorics.laurentPolynomialSmul p f = 0 := by
-- proof
  apply AlgebraicCombinatorics.torsion_example

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma bounded_sum_eq_eq
-- given
  (r : AlgebraicCombinatorics.BalancedTernaryRepresentation n)
  (k : ℕ)
  (hk : r.isBounded k) :
-- imply
  n = ∑ i ∈ Finset.range (k + 1), (r.digits i).toInt * (3 : ℤ) ^ i := by
-- proof
  apply AlgebraicCombinatorics.bounded_sum_eq r k hk

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma sum_powers_of_three_eq_zero_eq
-- given
  (k : ℕ)
  (c : ℕ → ℤ)
  (hc : ∀ i ≤ k, -2 ≤ c i ∧ c i ≤ 2)
  (hzero : ∀ i > k, c i = 0)
  (hsum : ∑ i ∈ Finset.range (k + 1), c i * (3 : ℤ) ^ i = 0) :
-- imply
  ∀ i, c i = 0 := by
-- proof
  apply AlgebraicCombinatorics.sum_powers_of_three_eq_zero k c hc hzero hsum

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma balanced_ternary_representation_bounded_unique_eq
-- given
  (k : ℕ)
  (n : ℤ)
  (r₁ r₂ : AlgebraicCombinatorics.BalancedTernaryRepresentation n)
  (hn : |n| ≤ ∑ i ∈ Finset.range (k + 1), (3 : ℤ) ^ i)
  (h₀ : r₁.isBounded k)
  (h₁ : r₂.isBounded k) :
-- imply
  r₁.digits = r₂.digits := by
-- proof
  apply AlgebraicCombinatorics.balancedTernaryRepresentation_bounded_unique k n hn r₁ r₂ h₀ h₁

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma one_plus_t_plus_tinv_eq_eq
-- given
  (K : Type*)
  [CommRing K] :
-- imply
  (1 + LaurentPolynomial.T 1 + LaurentPolynomial.T (-1) : LaurentPolynomial K) *
    (LaurentPolynomial.T 1 * (1 - LaurentPolynomial.T 1)) = 1 - LaurentPolynomial.T 3 := by
-- proof
  apply AlgebraicCombinatorics.one_plus_T_plus_Tinv_eq K

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma geom_sum_three_eq
-- given
  (k : ℕ) :
-- imply
  2 * ∑ i ∈ Finset.range (k + 1), (3 : ℤ) ^ i = (3 : ℤ) ^ (k + 1) - 1 := by
-- proof
  apply AlgebraicCombinatorics.geom_sum_three k

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma pv_bitsFromList_support_finite
-- given
  (L : List ℕ)
  (hL : ∀ x ∈ L, x < 2) :
-- imply
  {i | bitsFromList L hL i ≠ 0}.Finite := by
-- proof
  apply AlgebraicCombinatorics.BinaryRepresentation.bitsFromList_support_finite L hL

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma pv_bitsFromList_of_lt
  {L : List ℕ}
  {hL : ∀ x ∈ L, x < 2}
  {i : ℕ}
-- given
  (hi : i < L.length) :
-- imply
  (bitsFromList L hL i : ℕ) = L[i] := by
-- proof
  apply AlgebraicCombinatorics.BinaryRepresentation.bitsFromList_of_lt hi

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma pv_bitsFromList_of_ge
  {L : List ℕ}
  {hL : ∀ x ∈ L, x < 2}
  {i : ℕ}
-- given
  (hi : L.length ≤ i) :
-- imply
  bitsFromList L hL i = 0 := by
-- proof
  apply AlgebraicCombinatorics.BinaryRepresentation.bitsFromList_of_ge hi

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma pv_bitsFromList_sum_eq
-- given
  (L : List ℕ)
  (hL : ∀ x ∈ L, x < 2) :
-- imply
  finsum (fun i => (bitsFromList L hL i : ℕ) * 2^i) = Nat.ofDigits 2 L := by
-- proof
  apply AlgebraicCombinatorics.BinaryRepresentation.bitsFromList_sum_eq L hL

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma pv_support_mul_pow_subset
-- given
  (bits : ℕ → Fin 2) :
-- imply
  {i : ℕ | (bits i : ℕ) * 2^i ≠ 0} ⊆ {i | bits i ≠ 0} := by
-- proof
  apply AlgebraicCombinatorics.support_mul_pow_subset bits

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma pv_bits_zero_eq_mod
-- given
  (n : ℕ)
  (r : BinaryRepresentation n) :
-- imply
  (r.bits 0 : ℕ) = n % 2 := by
-- proof
  apply AlgebraicCombinatorics.bits_zero_eq_mod n r

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma pv_bits_eq_zero_of_sum_eq_zero
  {r : BinaryRepresentation 0}
-- given
  (i : ℕ) :
-- imply
  r.bits i = 0 := by
-- proof
  apply AlgebraicCombinatorics.bits_eq_zero_of_sum_eq_zero i

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma pv_sum_decomposition
-- given
  (bits : ℕ → Fin 2)
  (hfin : {i | bits i ≠ 0}.Finite) :
-- imply
  finsum (fun i => (bits i : ℕ) * 2^i) = (bits 0 : ℕ) + 2 * finsum (fun i => (bits (i + 1) : ℕ) * 2^i) := by
-- proof
  apply AlgebraicCombinatorics.sum_decomposition bits hfin

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma pv_digitOfMod3_spec
-- given
  (n : ℤ) :
-- imply
  (n - (digitOfMod3 n).toInt) % 3 = 0 := by
-- proof
  apply AlgebraicCombinatorics.digitOfMod3_spec n

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma pv_abs_div_three_lt
-- given
  (n : ℤ)
  (hn : n ≠ 0) :
-- imply
  |(n - (digitOfMod3 n).toInt) / 3| < |n| := by
-- proof
  apply AlgebraicCombinatorics.abs_div_three_lt n hn

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma pv_prependDigits_zero
-- given
  (d : BalancedTernaryDigit)
  (f : ℕ → BalancedTernaryDigit) :
-- imply
  prependDigits d f 0 = d := by
-- proof
  apply AlgebraicCombinatorics.prependDigits_zero d f

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma pv_prependDigits_succ
-- given
  (d : BalancedTernaryDigit)
  (f : ℕ → BalancedTernaryDigit)
  (i : ℕ) :
-- imply
  prependDigits d f (i + 1) = f i := by
-- proof
  apply AlgebraicCombinatorics.prependDigits_succ d f i

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma pv_prependDigits_finite_support
-- given
  (f : ℕ → BalancedTernaryDigit)
  (hf : {i | f i ≠ 0}.Finite)
  (d : BalancedTernaryDigit) :
-- imply
  {i | prependDigits d f i ≠ 0}.Finite := by
-- proof
  apply AlgebraicCombinatorics.prependDigits_finite_support d f hf

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma pv_prependDigits_sum
-- given
  (f : ℕ → BalancedTernaryDigit)
  (hf : {i | f i ≠ 0}.Finite)
  (d : BalancedTernaryDigit) :
-- imply
  finsum (fun i => (prependDigits d f i).toInt * (3 : ℤ)^i) = d.toInt + 3 * finsum (fun i => (f i).toInt * (3 : ℤ)^i) := by
-- proof
  apply AlgebraicCombinatorics.prependDigits_sum d f hf

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma pv_natAbs_of_nonneg_eq_toNat
-- given
  (m : ℤ)
  (hm : 0 ≤ m) :
-- imply
  m.natAbs = m.toNat := by
-- proof
  apply AlgebraicCombinatorics.natAbs_of_nonneg_eq_toNat m hm

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma pv_natAbs_lt_of_abs_lt
-- given
  (m n : ℤ)
  (h : |m| < |n|)
  (hn0 : n ≠ 0) :
-- imply
  m.natAbs < n.natAbs := by
-- proof
  apply AlgebraicCombinatorics.natAbs_lt_of_abs_lt m n h hn0

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma pv_sum_powers_of_three_eq_zero_aux
-- given
  (k : ℕ)
  (c : ℕ → ℤ)
  (hc : ∀ i ≤ k, -2 ≤ c i ∧ c i ≤ 2)
  (hzero : ∀ i > k, c i = 0)
  (hsum : ∑ i ∈ Finset.range (k + 1), c i * (3 : ℤ)^i = 0) :
-- imply
  ∀ i, c i = 0 := by
-- proof
  apply AlgebraicCombinatorics.sum_powers_of_three_eq_zero_aux k c hc hzero hsum


-- created on 2026-10-11
-- updated on 2026-10-26
