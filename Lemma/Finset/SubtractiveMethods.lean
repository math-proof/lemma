import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.SubtractiveMethods.Part3
open scoped BigOperators
open AlgebraicCombinatorics.SubtractiveMethods


section
-- ac-theorems


open Finset BigOperators

namespace AlgebraicCombinatorics.SubtractiveMethods

/-- A tuple is all-even iff all multiplicities are even -/
lemma isAllEven_iff_multiplicity {n d : ℕ} (x : Fin n → Fin d) :
    IsAllEven x ↔ ∀ k : Fin d, Even (multiplicity x k) := by
  rfl

@[simp]
lemma toSign_zero : toSign 0 = 1 := rfl

@[simp]
lemma toSign_one : toSign 1 = -1 := rfl


/-- The square of any sign is 1 -/
lemma toSign_sq (b : ZMod 2) : toSign b ^ 2 = 1 := by
  fin_cases b <;> simp [toSign]

/-- Even powers of a sign equal 1 -/
lemma toSign_pow_even (b : ZMod 2) (m : ℕ) (hm : Even m) : toSign b ^ m = 1 := by
  obtain ⟨k, hk⟩ := hm
  calc toSign b ^ m = toSign b ^ (2 * k) := by rw [hk, two_mul]
    _ = (toSign b ^ 2) ^ k := by ring
    _ = 1 ^ k := by rw [toSign_sq]
    _ = 1 := one_pow k

/-- Odd powers of a sign equal the sign itself -/
lemma toSign_pow_odd (b : ZMod 2) (m : ℕ) (hm : Odd m) : toSign b ^ m = toSign b := by
  obtain ⟨k, hk⟩ := hm
  calc toSign b ^ m = toSign b ^ (2 * k + 1) := by rw [hk, two_mul]
    _ = (toSign b ^ 2) ^ k * toSign b := by ring
    _ = 1 ^ k * toSign b := by rw [toSign_sq]
    _ = toSign b := by ring

/-- Adding 1 in ZMod 2 flips the sign -/
lemma toSign_add_one (b : ZMod 2) : toSign (b + 1) = -toSign b := by
  fin_cases b <;> decide

/-- The product can be rewritten in terms of multiplicities:
`∏_i e_{x_i} = ∏_k e_k^{m_k}` where `m_k` is the multiplicity of `k` in `x`.

Label: Equation `pf.lem.cancel.all-even.l2.e=e` -/
lemma signProduct_eq_prod_pow {n d : ℕ} (e : Fin d → ZMod 2) (x : Fin n → Fin d) :
    signProduct e x = ∏ k : Fin d, (toSign (e k)) ^ (multiplicity x k) := by
  unfold signProduct multiplicity
  rw [← Finset.prod_fiberwise Finset.univ x (fun i => toSign (e (x i)))]
  congr 1
  ext k
  simp only [prod_filter]
  have h1 : ∏ a : Fin n, (if x a = k then toSign (e (x a)) else 1) =
            ∏ a : Fin n, (if x a = k then toSign (e k) else 1) := by
    apply Finset.prod_congr rfl
    intro a _
    split_ifs with h
    · rw [h]
    · rfl
  rw [h1]
  rw [Finset.prod_ite]
  simp only [prod_const_one, mul_one]
  rw [Finset.prod_const]

/-- Sum interchange identity (Lemma `lem.cancel.all-even.l1`):
The sum over sign tuples of `(∑_k e_k)^n` equals the double sum
over index tuples and sign tuples of the sign product.

This follows from expanding `(∑_k e_k)^n` using the distributive law.

Label: Lemma `lem.cancel.all-even.l1` -/
lemma sum_signSum_pow_eq_sum_signProduct (n d : ℕ) :
    ∑ e : Fin d → ZMod 2, (signSum e)^n =
    ∑ x : Fin n → Fin d, ∑ e : Fin d → ZMod 2, signProduct e x := by
  -- Unfold the definitions
  simp only [signSum, signProduct]
  -- Expand (∑ k, toSign (e k))^n as ∑_{x : Fin n → Fin d} ∏ i, toSign (e (x i))
  -- using the product rule (generalized distributive law)
  simp_rw [Finset.sum_pow']
  -- Convert piFinset over univ to the full type
  simp only [Fintype.piFinset_univ]
  -- Interchange the order of summation
  rw [Finset.sum_comm]

/-- flipSign is an involution -/
lemma flipSign_involutive {d : ℕ} (k : Fin d) : Function.Involutive (flipSign k) := by
  intro e
  ext j
  simp only [flipSign, Function.update]
  split_ifs with h
  · subst h
    have h2 : (2 : ZMod 2) = 0 := by decide
    calc e j + 1 + 1 = e j + 2 := by ring
      _ = e j + 0 := by rw [h2]
      _ = e j := by ring
  · rfl

/-- flipSign produces a different tuple -/
lemma flipSign_ne {d : ℕ} (k : Fin d) (e : Fin d → ZMod 2) : flipSign k e ≠ e := by
  intro h
  have h1 : (flipSign k e) k = e k := by rw [h]
  simp only [flipSign, Function.update_self] at h1
  have : (1 : ZMod 2) = 0 := by
    calc (1 : ZMod 2) = (e k + 1) - e k := by ring
      _ = e k - e k := by rw [h1]
      _ = 0 := by ring
  exact one_ne_zero this

/-- flipSign at position k gives e_k + 1 at position k -/
lemma flipSign_self {d : ℕ} (k : Fin d) (e : Fin d → ZMod 2) :
    (flipSign k e) k = e k + 1 := by
  simp [flipSign]

/-- flipSign at position k leaves other positions unchanged -/
lemma flipSign_ne_self {d : ℕ} (k j : Fin d) (e : Fin d → ZMod 2) (h : j ≠ k) :
    (flipSign k e) j = e j := by
  simp [flipSign, Function.update_of_ne h]

/-- Key lemma: flipping sign k negates the sign product when k has odd multiplicity -/
lemma signProduct_flipSign {n d : ℕ} (e : Fin d → ZMod 2) (x : Fin n → Fin d)
    (k : Fin d) (hk : Odd (multiplicity x k)) :
    signProduct (flipSign k e) x = -signProduct e x := by
  rw [signProduct_eq_prod_pow, signProduct_eq_prod_pow]
  -- Split the product at k
  rw [← Finset.prod_erase_mul (univ) _ (Finset.mem_univ k)]
  rw [← Finset.prod_erase_mul (univ) _ (Finset.mem_univ k)]
  have h2 : ∏ j ∈ univ.erase k, toSign ((flipSign k e) j) ^ multiplicity x j =
            ∏ j ∈ univ.erase k, toSign (e j) ^ multiplicity x j := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [flipSign_ne_self k j e (Finset.ne_of_mem_erase hj)]
  rw [h2]
  -- Now handle the k-th factor
  rw [flipSign_self, toSign_add_one]
  rw [Odd.neg_pow hk]
  ring

/-- If an n-tuple is not all-even, then the sum over all sign tuples
of the sign product is zero (Lemma `lem.cancel.all-even.l2(a)`).

The proof uses an involution argument: if some element `k` has odd
multiplicity, flipping the sign of `e_k` negates the product, so
terms cancel in pairs.

Label: Lemma `lem.cancel.all-even.l2(a)` -/
lemma sum_signProduct_not_allEven {n d : ℕ} (x : Fin n → Fin d) (hx : ¬IsAllEven x) :
    ∑ e : Fin d → ZMod 2, signProduct e x = 0 := by
  -- There exists k with odd multiplicity
  simp only [IsAllEven, not_forall] at hx
  obtain ⟨k, hk⟩ := hx
  rw [Nat.not_even_iff_odd] at hk
  -- Use the involution flipSign k
  apply Finset.sum_involution (fun e _ => flipSign k e)
  · -- signProduct e + signProduct (flipSign k e) = 0
    intro e _
    rw [signProduct_flipSign e x k hk]
    ring
  · -- flipSign k e ≠ e
    intro e _ _
    exact flipSign_ne k e
  · -- flipSign k e ∈ univ
    intro e _
    exact Finset.mem_univ _
  · -- flipSign is involutive
    intro e _
    exact flipSign_involutive k e

/-- If an n-tuple is all-even, then the sum over all sign tuples
of the sign product equals 2^d (Lemma `lem.cancel.all-even.l2(b)`).

The proof: when all multiplicities are even, each `e_k^{m_k} = 1`
(since `(±1)^{even} = 1`), so every sign product equals 1, and
there are 2^d sign tuples.

Label: Lemma `lem.cancel.all-even.l2(b)` -/
lemma sum_signProduct_allEven {n d : ℕ} (x : Fin n → Fin d) (hx : IsAllEven x) :
    ∑ e : Fin d → ZMod 2, signProduct e x = 2^d := by
  -- When all multiplicities are even, each signProduct equals 1
  have h : ∀ e : Fin d → ZMod 2, signProduct e x = 1 := by
    intro e
    rw [signProduct_eq_prod_pow]
    apply Finset.prod_eq_one
    intro k _
    apply toSign_pow_even
    exact hx k
  simp only [h, sum_const]
  have card_eq : (univ : Finset (Fin d → ZMod 2)).card = 2^d := by
    simp [ZMod.card]
  simp [card_eq]

/-- For a sign tuple corresponding to subset S, the sum of entries
equals `d - 2|S|`. -/
lemma signSum_eq_card {d : ℕ} (e : Fin d → ZMod 2) :
    signSum e = d - 2 * (signTupleToSubset e).card := by
  unfold signSum signTupleToSubset
  -- toSign can be written as 1 - 2 * (if e k = 1 then 1 else 0)
  have htoSign : ∀ k, toSign (e k) = 1 - 2 * (if e k = 1 then 1 else 0) := by
    intro k
    unfold toSign
    have hlt : (e k).val < 2 := (e k).isLt
    interval_cases h : (e k).val
    · have he : e k = 0 := Fin.ext h
      simp [he]
    · have he : e k = 1 := Fin.ext h
      simp [he]
  have heq : ∑ k : Fin d, toSign (e k) = ∑ k : Fin d, (1 - 2 * (if e k = 1 then 1 else 0)) := by
    apply sum_congr rfl
    intro k _
    exact htoSign k
  rw [heq]
  simp only [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  congr 1
  rw [← mul_sum, sum_boole]

/-- For a subset S, the sign sum of the corresponding tuple equals d - 2|S| -/
lemma signSum_subsetToSignTuple {d : ℕ} (S : Finset (Fin d)) :
    signSum (subsetToSignTuple S) = d - 2 * S.card := by
  rw [signSum_eq_card, signTupleToSubset_subsetToSignTuple]

/-- Compute the double sum using lemma l2 -/
lemma sum_signProduct_eq_allEven_count (n d : ℕ) :
    ∑ x : Fin n → Fin d, ∑ e : Fin d → ZMod 2, signProduct e x =
    (allEvenTuples n d).card * 2^d := by
  -- Split into all-even and not-all-even tuples
  have h1 : ∑ x : Fin n → Fin d, ∑ e : Fin d → ZMod 2, signProduct e x =
      ∑ x ∈ (univ : Finset (Fin n → Fin d)).filter IsAllEven, ∑ e : Fin d → ZMod 2, signProduct e x +
      ∑ x ∈ (univ : Finset (Fin n → Fin d)).filter (fun x => ¬IsAllEven x), ∑ e : Fin d → ZMod 2, signProduct e x := by
    rw [← sum_filter_add_sum_filter_not (univ : Finset (Fin n → Fin d)) IsAllEven]
  rw [h1]
  -- The non-all-even part is 0
  have h2 : ∑ x ∈ (univ : Finset (Fin n → Fin d)).filter (fun x => ¬IsAllEven x),
      ∑ e : Fin d → ZMod 2, signProduct e x = 0 := by
    apply sum_eq_zero
    intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    exact sum_signProduct_not_allEven x hx
  rw [h2, add_zero]
  -- The all-even part is |allEvenTuples| * 2^d
  have h3 : ∑ x ∈ (univ : Finset (Fin n → Fin d)).filter IsAllEven,
      ∑ e : Fin d → ZMod 2, signProduct e x =
      ∑ x ∈ allEvenTuples n d, (2 : ℤ)^d := by
    apply sum_congr
    · rfl
    intro x hx
    simp only [mem_filter, mem_univ, true_and, allEvenTuples] at hx
    exact sum_signProduct_allEven x hx
  rw [h3]
  simp [allEvenTuples, sum_const, mul_comm]

/-- Rewrite sum over sign tuples as sum over subsets -/
lemma sum_signSum_pow_eq_sum_subset (n d : ℕ) :
    ∑ e : Fin d → ZMod 2, (signSum e)^n =
    ∑ S : Finset (Fin d), (d - 2 * S.card : ℤ)^n := by
  rw [Fintype.sum_equiv (signTupleEquivSubset d)]
  intro e
  rw [signSum_eq_card]
  simp [signTupleEquivSubset]

/-- Group sum over subsets by cardinality -/
lemma sum_subset_eq_sum_choose (n d : ℕ) :
    ∑ S : Finset (Fin d), (d - 2 * S.card : ℤ)^n =
    ∑ k ∈ range (d + 1), d.choose k * (d - 2*k : ℤ)^n := by
  have h1 : ∑ S : Finset (Fin d), (d - 2 * S.card : ℤ)^n =
      ∑ k ∈ range (d + 1), ∑ S ∈ (univ : Finset (Finset (Fin d))).filter (fun S => S.card = k),
        (d - 2 * S.card : ℤ)^n := by
    rw [← sum_fiberwise_of_maps_to (s := univ) (t := range (d + 1)) (g := fun S => S.card)]
    intro S _
    simp only [mem_range]
    have : S.card ≤ (univ : Finset (Fin d)).card := Finset.card_le_card (Finset.subset_univ S)
    simp only [card_univ, Fintype.card_fin] at this
    omega
  rw [h1]
  apply sum_congr rfl
  intro k hk
  simp only [mem_range] at hk
  have h2 : ∀ S ∈ (univ : Finset (Finset (Fin d))).filter (fun S => S.card = k),
      (d - 2 * S.card : ℤ)^n = (d - 2*k : ℤ)^n := by
    intro S hS
    simp only [mem_filter, mem_univ, true_and] at hS
    simp [hS]
  simp_rw [sum_congr rfl h2, sum_const]
  have h3 : ((univ : Finset (Finset (Fin d))).filter (fun S => S.card = k)).card = d.choose k := by
    have : (univ : Finset (Finset (Fin d))).filter (fun S => S.card = k) = powersetCard k (univ : Finset (Fin d)) := by
      ext S
      simp [mem_powersetCard]
    rw [this, card_powersetCard, card_univ, Fintype.card_fin]
  rw [h3]
  ring

/-- The main counting formula (Theorem `thm.cancel.all-even`):
The number of all-even n-tuples in `(Fin n → Fin d)` equals
`(1/2^d) ∑_{k=0}^d C(d,k) (d-2k)^n`.

This formula implies that `∑_{k=0}^d C(d,k) (d-2k)^n` is nonnegative
and divisible by `2^d`, which is not obvious from the formula itself
due to the alternating signs when `n` is odd.

Label: Theorem `thm.cancel.all-even` -/
lemma allEven_count_formula (n d : ℕ) :
    ((allEvenTuples n d).card : ℤ) * 2^d = ∑ k ∈ range (d + 1), d.choose k * (d - 2*k : ℤ)^n := by
  -- Connect via l1 and l2: LHS = ∑_x ∑_e signProduct e x = ∑_e (signSum e)^n = RHS
  have h1 : ((allEvenTuples n d).card : ℤ) * 2^d =
      ∑ x : Fin n → Fin d, ∑ e : Fin d → ZMod 2, signProduct e x := by
    rw [sum_signProduct_eq_allEven_count]
  rw [h1, ← sum_signSum_pow_eq_sum_signProduct, sum_signSum_pow_eq_sum_subset, sum_subset_eq_sum_choose]

/-- Corollary: The sum `∑_{k=0}^d C(d,k) (d-2k)^n` is divisible by `2^d`. -/
lemma sum_choose_pow_dvd_pow_two (n d : ℕ) :
    (2^d : ℤ) ∣ ∑ k ∈ range (d + 1), d.choose k * (d - 2*k : ℤ)^n := by
  rw [← allEven_count_formula n d]
  exact dvd_mul_left ((2 : ℤ)^d) ((allEvenTuples n d).card)

/-- Corollary: The sum `∑_{k=0}^d C(d,k) (d-2k)^n` is nonnegative. -/
lemma sum_choose_pow_nonneg (n d : ℕ) :
    0 ≤ ∑ k ∈ range (d + 1), d.choose k * (d - 2*k : ℤ)^n := by
  rw [← allEven_count_formula]
  exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num : (0 : ℤ) ≤ 2) d)

end AlgebraicCombinatorics.SubtractiveMethods
end


/--
[SubtractiveMethods](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/SubtractiveMethods.lean)
-/
@[path]
private lemma pv_isAllEven_iff_multiplicity
-- given
  {n d : ℕ}
  (x : Fin n → Fin d) :
-- imply
  IsAllEven x ↔ ∀ k : Fin d, Even (multiplicity x k) := by
-- proof
  apply AlgebraicCombinatorics.SubtractiveMethods.isAllEven_iff_multiplicity

/--
[SubtractiveMethods](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/SubtractiveMethods.lean)
-/
@[path]
private lemma pv_toSign_zero :
-- imply
  toSign 0 = 1 := by
-- proof
  apply AlgebraicCombinatorics.SubtractiveMethods.toSign_zero

/--
[SubtractiveMethods](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/SubtractiveMethods.lean)
-/
@[path]
private lemma pv_toSign_one :
-- imply
  toSign 1 = -1 := by
-- proof
  apply AlgebraicCombinatorics.SubtractiveMethods.toSign_one

/--
[SubtractiveMethods](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/SubtractiveMethods.lean)
-/
@[path]
private lemma pv_toSign_sq
-- given
  (b : ZMod 2) :
-- imply
  toSign b ^ 2 = 1 := by
-- proof
  apply AlgebraicCombinatorics.SubtractiveMethods.toSign_sq

/--
[SubtractiveMethods](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/SubtractiveMethods.lean)
-/
@[path]
private lemma pv_toSign_pow_even
-- given
  (b : ZMod 2)
  (m : ℕ)
  (hm : Even m) :
-- imply
  toSign b ^ m = 1 := by
-- proof
  apply AlgebraicCombinatorics.SubtractiveMethods.toSign_pow_even b m hm

/--
[SubtractiveMethods](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/SubtractiveMethods.lean)
-/
@[path]
private lemma pv_toSign_pow_odd
-- given
  (b : ZMod 2)
  (m : ℕ)
  (hm : Odd m) :
-- imply
  toSign b ^ m = toSign b := by
-- proof
  apply AlgebraicCombinatorics.SubtractiveMethods.toSign_pow_odd b m hm

/--
[SubtractiveMethods](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/SubtractiveMethods.lean)
-/
@[path]
private lemma pv_toSign_add_one
-- given
  (b : ZMod 2) :
-- imply
  toSign (b + 1) = -toSign b := by
-- proof
  apply AlgebraicCombinatorics.SubtractiveMethods.toSign_add_one

/--
[SubtractiveMethods](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/SubtractiveMethods.lean)
-/
@[path]
private lemma pv_signProduct_eq_prod_pow
-- given
  {n d : ℕ}
  (e : Fin d → ZMod 2)
  (x : Fin n → Fin d) :
-- imply
  signProduct e x = ∏ k : Fin d, (toSign (e k)) ^ (multiplicity x k) := by
-- proof
  apply AlgebraicCombinatorics.SubtractiveMethods.signProduct_eq_prod_pow

/--
[SubtractiveMethods](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/SubtractiveMethods.lean)
-/
@[path]
private lemma pv_sum_signSum_pow_eq_sum_signProduct
-- given
  (n d : ℕ) :
-- imply
  ∑ e : Fin d → ZMod 2, (signSum e) ^ n =
    ∑ x : Fin n → Fin d, ∑ e : Fin d → ZMod 2, signProduct e x := by
-- proof
  apply AlgebraicCombinatorics.SubtractiveMethods.sum_signSum_pow_eq_sum_signProduct

/--
[SubtractiveMethods](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/SubtractiveMethods.lean)
-/
@[path]
private lemma pv_flipSign_involutive
-- given
  {d : ℕ}
  (k : Fin d) :
-- imply
  Function.Involutive (flipSign k) := by
-- proof
  apply AlgebraicCombinatorics.SubtractiveMethods.flipSign_involutive

/--
[SubtractiveMethods](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/SubtractiveMethods.lean)
-/
@[path]
private lemma pv_flipSign_ne
-- given
  {d : ℕ}
  (k : Fin d)
  (e : Fin d → ZMod 2) :
-- imply
  flipSign k e ≠ e := by
-- proof
  apply AlgebraicCombinatorics.SubtractiveMethods.flipSign_ne

/--
[SubtractiveMethods](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/SubtractiveMethods.lean)
-/
@[path]
private lemma pv_flipSign_self
-- given
  {d : ℕ}
  (k : Fin d)
  (e : Fin d → ZMod 2) :
-- imply
  (flipSign k e) k = e k + 1 := by
-- proof
  apply AlgebraicCombinatorics.SubtractiveMethods.flipSign_self

/--
[SubtractiveMethods](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/SubtractiveMethods.lean)
-/
@[path]
private lemma pv_flipSign_ne_self
-- given
  {d : ℕ}
  (k j : Fin d)
  (h : j ≠ k)
  (e : Fin d → ZMod 2) :
-- imply
  (flipSign k e) j = e j := by
-- proof
  apply AlgebraicCombinatorics.SubtractiveMethods.flipSign_ne_self k j e h

/--
[SubtractiveMethods](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/SubtractiveMethods.lean)
-/
@[path]
private lemma pv_signProduct_flipSign
-- given
  {n d : ℕ}
  (e : Fin d → ZMod 2)
  (x : Fin n → Fin d)
  (k : Fin d)
  (hk : Odd (multiplicity x k)) :
-- imply
  signProduct (flipSign k e) x = -signProduct e x := by
-- proof
  apply AlgebraicCombinatorics.SubtractiveMethods.signProduct_flipSign e x k hk

/--
[SubtractiveMethods](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/SubtractiveMethods.lean)
-/
@[path]
private lemma pv_sum_signProduct_not_allEven
-- given
  {n d : ℕ}
  (x : Fin n → Fin d)
  (hx : ¬IsAllEven x) :
-- imply
  ∑ e : Fin d → ZMod 2, signProduct e x = 0 := by
-- proof
  apply AlgebraicCombinatorics.SubtractiveMethods.sum_signProduct_not_allEven x hx

/--
[SubtractiveMethods](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/SubtractiveMethods.lean)
-/
@[path]
private lemma pv_sum_signProduct_allEven
-- given
  {n d : ℕ}
  (x : Fin n → Fin d)
  (hx : IsAllEven x) :
-- imply
  ∑ e : Fin d → ZMod 2, signProduct e x = 2 ^ d := by
-- proof
  apply AlgebraicCombinatorics.SubtractiveMethods.sum_signProduct_allEven x hx

/--
[SubtractiveMethods](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/SubtractiveMethods.lean)
-/
@[path]
private lemma pv_signSum_eq_card
-- given
  {d : ℕ}
  (e : Fin d → ZMod 2) :
-- imply
  signSum e = d - 2 * (signTupleToSubset e).card := by
-- proof
  apply AlgebraicCombinatorics.SubtractiveMethods.signSum_eq_card

/--
[SubtractiveMethods](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/SubtractiveMethods.lean)
-/
@[path]
private lemma signTupleToSubset_subsetToSignTuple
-- given
  {d : ℕ}
  (S : Finset (Fin d)) :
-- imply
  signTupleToSubset (subsetToSignTuple S) = S := by
-- proof
  apply AlgebraicCombinatorics.SubtractiveMethods.signTupleToSubset_subsetToSignTuple

/--
[SubtractiveMethods](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/SubtractiveMethods.lean)
-/
@[path]
private lemma subsetToSignTuple_signTupleToSubset
-- given
  {d : ℕ}
  (e : Fin d → ZMod 2) :
-- imply
  subsetToSignTuple (signTupleToSubset e) = e := by
-- proof
  apply AlgebraicCombinatorics.SubtractiveMethods.subsetToSignTuple_signTupleToSubset

/--
[SubtractiveMethods](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/SubtractiveMethods.lean)
-/
@[path]
private lemma pv_signSum_subsetToSignTuple
-- given
  {d : ℕ}
  (S : Finset (Fin d)) :
-- imply
  signSum (subsetToSignTuple S) = d - 2 * S.card := by
-- proof
  apply AlgebraicCombinatorics.SubtractiveMethods.signSum_subsetToSignTuple

/--
[SubtractiveMethods](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/SubtractiveMethods.lean)
-/
@[path]
private lemma pv_sum_signProduct_eq_allEven_count
-- given
  (n d : ℕ) :
-- imply
  ∑ x : Fin n → Fin d, ∑ e : Fin d → ZMod 2, signProduct e x =
    (allEvenTuples n d).card * 2 ^ d := by
-- proof
  apply AlgebraicCombinatorics.SubtractiveMethods.sum_signProduct_eq_allEven_count

/--
[SubtractiveMethods](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/SubtractiveMethods.lean)
-/
@[path]
private lemma pv_sum_signSum_pow_eq_sum_subset
-- given
  (n d : ℕ) :
-- imply
  ∑ e : Fin d → ZMod 2, (signSum e) ^ n =
    ∑ S : Finset (Fin d), (d - 2 * S.card : ℤ) ^ n := by
-- proof
  apply AlgebraicCombinatorics.SubtractiveMethods.sum_signSum_pow_eq_sum_subset

/--
[SubtractiveMethods](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/SubtractiveMethods.lean)
-/
@[path]
private lemma pv_sum_subset_eq_sum_choose
-- given
  (n d : ℕ) :
-- imply
  ∑ S : Finset (Fin d), (d - 2 * S.card : ℤ) ^ n =
    ∑ k ∈ Finset.range (d + 1), d.choose k * (d - 2 * k : ℤ) ^ n := by
-- proof
  apply AlgebraicCombinatorics.SubtractiveMethods.sum_subset_eq_sum_choose

/--
[SubtractiveMethods](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/SubtractiveMethods.lean)
-/
@[path]
private lemma pv_allEven_count_formula
-- given
  (n d : ℕ) :
-- imply
  ((allEvenTuples n d).card : ℤ) * 2 ^ d =
    ∑ k ∈ Finset.range (d + 1), d.choose k * (d - 2 * k : ℤ) ^ n := by
-- proof
  apply AlgebraicCombinatorics.SubtractiveMethods.allEven_count_formula

/--
[SubtractiveMethods](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/SubtractiveMethods.lean)
-/
@[path]
private lemma pv_sum_choose_pow_dvd_pow_two
-- given
  (n d : ℕ) :
-- imply
  (2 ^ d : ℤ) ∣ ∑ k ∈ Finset.range (d + 1), d.choose k * (d - 2 * k : ℤ) ^ n := by
-- proof
  apply AlgebraicCombinatorics.SubtractiveMethods.sum_choose_pow_dvd_pow_two

/--
[SubtractiveMethods](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/SubtractiveMethods.lean)
-/
@[path]
private lemma pv_sum_choose_pow_nonneg
-- given
  (n d : ℕ) :
-- imply
  0 ≤ ∑ k ∈ Finset.range (d + 1), d.choose k * (d - 2 * k : ℤ) ^ n := by
-- proof
  apply AlgebraicCombinatorics.SubtractiveMethods.sum_choose_pow_nonneg


-- created on 2026-10-20
