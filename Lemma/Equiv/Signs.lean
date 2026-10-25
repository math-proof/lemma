import Mathlib
import sympy.Basic
import Def.GroupTheory.Perm.Signs
import Lemma.Equiv.Inversions1


section
-- ac-theorems


open Equiv Equiv.Perm Finset BigOperators

variable {α : Type*} [DecidableEq α] [Fintype α]

namespace Equiv.Perm


section SignDefinition


variable {n : ℕ}

/-- The sign of a permutation equals (-1)^ℓ(σ) where ℓ(σ) is the number of inversions.

**Definition (def.perm.sign)**: The sign of σ ∈ Sₙ is defined as (-1)^ℓ(σ),
where ℓ(σ) is the length (number of inversions) of σ.

This theorem proves that Mathlib's `Equiv.Perm.sign` equals the textbook definition. -/
lemma sign_eq_neg_one_pow_invCount (σ : Perm (Fin n)) :
    sign σ = (-1 : ℤˣ) ^ AlgebraicCombinatorics.Perm.invCount σ := by
  rw [σ.sign_eq_prod_prod_Ioi]
  rw [Finset.prod_sigma']
  -- The product equals (-1)^(number of pairs where σ i ≥ σ j, i < j)
  -- Since σ is injective, this equals the number of inversions
  have key : ∀ (s : Finset (Σ _ : Fin n, Fin n)),
      (∏ x ∈ s, (if σ x.1 < σ x.2 then (1 : ℤˣ) else -1)) =
      (-1 : ℤˣ) ^ (s.filter (fun x => ¬ σ x.1 < σ x.2)).card := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | @insert a s' ha ih =>
      rw [Finset.prod_insert ha]
      by_cases h : σ a.1 < σ a.2
      · simp only [h, ↓reduceIte, one_mul]
        rw [Finset.filter_insert, ite_eq_right (by simp [h]), ih]
      · simp only [h, ↓reduceIte]
        rw [Finset.filter_insert, ite_eq_left (by simp [h])]
        rw [Finset.card_insert_of_notMem (by simp [ha])]
        rw [pow_succ, mul_comm, ih]
  rw [key]
  congr 1
  -- Show the count of non-lt pairs equals invCount
  rw [AlgebraicCombinatorics.Perm.invCount, AlgebraicCombinatorics.Perm.inv]
  have equiv_card : ((univ.sigma fun a => Ioi a).filter (fun x => ¬σ x.1 < σ x.2)).card =
      (Finset.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ σ p.1 > σ p.2) Finset.univ).card := by
    let e : (Σ _ : Fin n, Fin n) ≃ (Fin n × Fin n) := Equiv.sigmaEquivProd (Fin n) (Fin n)
    rw [← Finset.card_map e.toEmbedding]
    congr 1
    ext ⟨i, j⟩
    simp only [mem_map, mem_filter, mem_sigma, mem_univ, mem_Ioi, true_and, not_lt,
      Equiv.toEmbedding_apply]
    constructor
    · rintro ⟨⟨a, b⟩, ⟨⟨hab, hσ⟩, heq⟩⟩
      have heq' : (a, b) = (i, j) := heq
      simp only [Prod.mk.injEq] at heq'
      obtain ⟨rfl, rfl⟩ := heq'
      exact ⟨hab, lt_of_le_of_ne hσ (fun h => (ne_of_lt hab) (σ.injective h.symm))⟩
    · intro ⟨hij, hσ⟩
      exact ⟨⟨i, j⟩, ⟨⟨hij, le_of_lt hσ⟩, rfl⟩⟩
  exact equiv_card

/-- Corollary: sign as an integer equals (-1)^invCount.
**Definition (def.perm.sign)** -/
lemma sign_coe_eq_neg_one_pow_invCount (σ : Perm (Fin n)) :
    (sign σ : ℤ) = (-1 : ℤ) ^ AlgebraicCombinatorics.Perm.invCount σ := by
  rw [sign_eq_neg_one_pow_invCount]
  simp only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]

end SignDefinition

lemma isEven_iff_sign_eq_one {σ : Perm α} : σ.IsEven ↔ sign σ = 1 := Iff.rfl

lemma isOdd_iff_sign_eq_neg_one {σ : Perm α} : σ.IsOdd ↔ sign σ = -1 := Iff.rfl

lemma isEven_iff_mem_alternatingGroup {σ : Perm α} :
    σ.IsEven ↔ σ ∈ alternatingGroup α :=
  mem_alternatingGroup.symm

lemma isOdd_iff_not_mem_alternatingGroup {σ : Perm α} :
    σ.IsOdd ↔ σ ∉ alternatingGroup α := by
  rw [isOdd_iff_sign_eq_neg_one, mem_alternatingGroup]
  constructor
  · intro h hcontra
    rw [h] at hcontra
    exact absurd hcontra (by decide)
  · intro h
    rcases Int.units_eq_one_or (sign σ) with hsign | hsign
    · exact absurd hsign h
    · exact hsign

/-- The identity permutation is even.
This is a useful base case when reasoning about permutation parity. -/
@[simp]
lemma isEven_one : IsEven (1 : Perm α) := by
  simp [IsEven]

/-- The identity permutation is not odd. -/
@[simp]
lemma not_isOdd_one : ¬IsOdd (1 : Perm α) := by
  simp [IsOdd]

/-- A transposition (swap) is an odd permutation.
This provides a cleaner interface when working with the `IsOdd` predicate
rather than directly with sign values. -/
lemma isOdd_swap {x y : α} (hxy : x ≠ y) : IsOdd (swap x y) := by
  simp [IsOdd, sign_swap hxy]

/-- Every permutation is either even or odd.
This follows from the fact that sign takes values in {1, -1}. -/
lemma isEven_or_isOdd (σ : Perm α) : σ.IsEven ∨ σ.IsOdd := by
  rcases Int.units_eq_one_or (sign σ) with h | h
  · left; exact h
  · right; exact h

/-- A permutation cannot be both even and odd. -/
lemma not_isEven_and_isOdd (σ : Perm α) : ¬(σ.IsEven ∧ σ.IsOdd) := by
  rintro ⟨heven, hodd⟩
  rw [isEven_iff_sign_eq_one] at heven
  rw [isOdd_iff_sign_eq_neg_one] at hodd
  rw [heven] at hodd
  exact absurd hodd (by decide)


/-- **(a)** The sign of the identity permutation is 1.
**Proposition (prop.perm.sign.props)(a)** -/
lemma sign_id : sign (1 : Perm α) = 1 := sign_one

/-- **(b)** The sign of a transposition is -1.
**Proposition (prop.perm.sign.props)(b)** -/
lemma sign_transposition {x y : α} (hxy : x ≠ y) : sign (swap x y) = -1 :=
  sign_swap hxy

/-- **(c)** The sign of a k-cycle is (-1)^(k-1).
**Proposition (prop.perm.sign.props)(c)**

This follows from the fact that a k-cycle has support of size k and
sign(σ) = -(-1)^|support(σ)| for cycles. -/
lemma sign_isCycle {σ : Perm α} (hσ : σ.IsCycle) :
    sign σ = -(-1 : ℤˣ) ^ σ.support.card :=
  hσ.sign

/-- **(d)** The sign is multiplicative: sign(στ) = sign(σ) · sign(τ).
**Proposition (prop.perm.sign.props)(d)** -/
lemma sign_mul' (σ τ : Perm α) : sign (σ * τ) = sign σ * sign τ :=
  sign_mul σ τ

/-- **(e)** The sign of a product equals the product of signs.
**Proposition (prop.perm.sign.props)(e)** -/
lemma sign_prod_list (l : List (Perm α)) :
    sign l.prod = (l.map sign).prod := by
  induction l with
  | nil => simp
  | cons σ l ih => simp [sign_mul, ih]

/-- **(f)** The sign of the inverse equals the sign of the permutation.
**Proposition (prop.perm.sign.props)(f)** -/
lemma sign_inv' (σ : Perm α) : sign σ⁻¹ = sign σ :=
  sign_inv σ


/-- **(h)** Product of differences under permutation.
**Proposition (prop.perm.sign.props)(h)**

For any elements x₁, ..., xₙ of a commutative ring and σ ∈ Sₙ:
∏_{i < j} (x_{σ(i)} - x_{σ(j)}) = sign(σ) · ∏_{i < j} (xᵢ - xⱼ)
-/
lemma prod_diff_comp_perm {n : ℕ} {R : Type*} [CommRing R] (σ : Perm (Fin n)) (x : Fin n → R) :
    ∏ i, ∏ j ∈ Ioi i, (x (σ i) - x (σ j)) = sign σ * ∏ i, ∏ j ∈ Ioi i, (x i - x j) := by
  have hf : ∀ i j, x i - x j = -(x j - x i) := fun i j => by ring
  exact σ.prod_Ioi_comp_eq_sign_mul_prod hf

/-- **(g)** Sign as a product over pairs.
**Proposition (prop.perm.sign.props)(g)**

For σ ∈ Sₙ: sign(σ) = ∏_{1 ≤ i < j ≤ n} (σ(i) - σ(j)) / (i - j)

We state this in a slightly different but equivalent form using the indicator function. -/
lemma sign_eq_prod_pairs {n : ℕ} (σ : Perm (Fin n)) :
    sign σ = ∏ i, ∏ j ∈ Ioi i, (if σ i < σ j then 1 else -1) :=
  σ.sign_eq_prod_prod_Ioi


/-- **Corollary (cor.perm.sign.hom)**
The sign is a group homomorphism from Sₙ to {1, -1}.

In Mathlib, this is expressed by `Equiv.Perm.sign` being a `MonoidHom`. -/
lemma sign_hom_mul (σ τ : Perm α) : sign (σ * τ) = sign σ * sign τ :=
  sign_mul σ τ


/-- **Corollary (cor.perm.altgp)**
The set of all even permutations in Sₙ is a normal subgroup.
This is the alternating group Aₙ. -/
lemma alternatingGroup_isNormal : (alternatingGroup α).Normal :=
  alternatingGroup.normal


/-- **Corollary (cor.perm.num-even)**
The number of even permutations in Sₙ equals n!/2 for n ≥ 2.
More precisely, |Aₙ| = (card α)!/2. -/
lemma card_even_perms [Nontrivial α] :
    Fintype.card (alternatingGroup α) = (Fintype.card α).factorial / 2 :=
  card_alternatingGroup

/-- The number of odd permutations equals the number of even permutations.
This follows from the bijection σ ↦ σ * swap(a,b) for any distinct a, b. -/
lemma card_odd_eq_card_even [Nontrivial α] :
    (univ.filter fun σ : Perm α => sign σ = -1).card =
    (univ.filter fun σ : Perm α => sign σ = 1).card := by
  -- The bijection σ ↦ σ * s maps even to odd permutations
  obtain ⟨a, b, hab⟩ := exists_pair_ne α
  let s := swap a b
  have hs : sign s = -1 := sign_swap hab
  have hs_sq : s * s = 1 := swap_mul_self a b
  -- Define the bijection between even and odd permutations
  refine Finset.card_bij (fun σ _ => σ * s) ?_ ?_ ?_ |>.symm
  · intro σ hσ
    simp only [mem_filter, mem_univ, true_and] at hσ ⊢
    rw [sign_mul, hσ, hs, one_mul]
  · intro σ₁ _ σ₂ _ h
    exact mul_right_cancel h
  · intro τ hτ
    simp only [mem_filter, mem_univ, true_and] at hτ ⊢
    refine ⟨τ * s, ?_, ?_⟩
    · rw [sign_mul, hτ, hs]
      decide
    · rw [mul_assoc, hs_sq, mul_one]

/-- **Equation (eq.cor.perm.num-even.sum-sign)**
The sum of signs over all permutations is 0 for n ≥ 2.

∑_{σ ∈ Sₙ} sign(σ) = 0 for n ≥ 2
-/
lemma sum_sign_eq_zero [Nontrivial α] :
    ∑ σ : Perm α, (sign σ : ℤ) = 0 := by
  -- The sum equals (# even) * 1 + (# odd) * (-1)
  -- Since # even = # odd, this is 0
  have hodd_card := card_odd_eq_card_even (α := α)
  -- Split sum by sign value
  let evenPerms := (univ : Finset (Perm α)).filter (fun σ => sign σ = 1)
  let oddPerms := (univ : Finset (Perm α)).filter (fun σ => sign σ = -1)
  have hsplit : ∑ σ : Perm α, (sign σ : ℤ) =
      ∑ σ ∈ evenPerms, (sign σ : ℤ) + ∑ σ ∈ oddPerms, (sign σ : ℤ) := by
    rw [← sum_filter_add_sum_filter_not univ (fun σ : Perm α => sign σ = 1)]
    congr 1
    apply sum_congr
    · ext σ
      simp only [mem_filter, mem_univ, true_and, oddPerms]
      constructor
      · intro h
        rcases Int.units_eq_one_or (sign σ) with hs | hs
        · exact absurd hs h
        · exact hs
      · intro h hcontra
        rw [hcontra] at h
        exact absurd h (by decide)
    · intro _ _; rfl
  rw [hsplit]
  have heven_sum : ∑ σ ∈ evenPerms, (sign σ : ℤ) = evenPerms.card := by
    trans ∑ _ ∈ evenPerms, (1 : ℤ)
    · apply sum_congr rfl
      intro σ hσ
      simp only [mem_filter, mem_univ, true_and, evenPerms] at hσ
      simp [hσ]
    · simp
  have hodd_sum : ∑ σ ∈ oddPerms, (sign σ : ℤ) = -(oddPerms.card : ℤ) := by
    trans ∑ _ ∈ oddPerms, (-1 : ℤ)
    · apply sum_congr rfl
      intro σ hσ
      simp only [mem_filter, mem_univ, true_and, oddPerms] at hσ
      simp [hσ]
    · simp
  rw [heven_sum, hodd_sum, hodd_card]
  ring


/-- **Proposition (prop.perm.sign.X)(a)**
The sign of a permutation of a finite set is independent of the chosen bijection.

For any bijections φ₁, φ₂ : X → [n], we have sign_{φ₁}(σ) = sign_{φ₂}(σ). -/
lemma sign_conj_eq {β : Type*} [DecidableEq β] [Fintype β]
    (σ : Perm α) (e : α ≃ β) :
    sign ((e.symm.trans σ).trans e) = sign σ :=
  sign_symm_trans_trans σ e

/-- **Proposition (prop.perm.sign.X)(b)**
The identity permutation of any finite set has sign 1. -/
lemma sign_id_finiteSet : sign (1 : Perm α) = 1 := sign_one

/-- **Proposition (prop.perm.sign.X)(c)**
The sign is multiplicative for permutations of any finite set. -/
lemma sign_mul_finiteSet (σ τ : Perm α) :
    sign (σ * τ) = sign σ * sign τ := sign_mul σ τ

end Equiv.Perm
end


/--
[Signs](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Signs.lean)
-/
@[path]
private lemma sign_eq_neg_one_pow_inv_count_eq
  (σ : Equiv.Perm (Fin n)) :
-- imply
  Equiv.Perm.sign σ = (-1 : ℤˣ) ^ AlgebraicCombinatorics.Perm.invCount σ := by
-- proof
  apply Equiv.Perm.sign_eq_neg_one_pow_invCount σ

/--
[Signs](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Signs.lean)
-/
@[path]
private lemma sign_coe_eq_neg_one_pow_inv_count_eq
  (σ : Equiv.Perm (Fin n)) :
-- imply
  (Equiv.Perm.sign σ : ℤ) = (-1 : ℤ) ^ AlgebraicCombinatorics.Perm.invCount σ := by
-- proof
  apply Equiv.Perm.sign_coe_eq_neg_one_pow_invCount σ

/--
[Signs](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Signs.lean)
-/
@[path]
private lemma is_even_iff_sign_eq_one_iff
  [DecidableEq α]
  [Fintype α]
  (σ : Equiv.Perm α) :
-- imply
  σ.IsEven ↔ Equiv.Perm.sign σ = 1 := by
-- proof
  apply Equiv.Perm.isEven_iff_sign_eq_one

/--
[Signs](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Signs.lean)
-/
@[path]
private lemma is_odd_iff_sign_eq_neg_one_iff
  [DecidableEq α]
  [Fintype α]
  (σ : Equiv.Perm α) :
-- imply
  σ.IsOdd ↔ Equiv.Perm.sign σ = -1 := by
-- proof
  apply Equiv.Perm.isOdd_iff_sign_eq_neg_one

/--
[Signs](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Signs.lean)
-/
@[path]
private lemma is_even_iff_mem_alternating_group_iff
  [DecidableEq α]
  [Fintype α]
  (σ : Equiv.Perm α) :
-- imply
  σ.IsEven ↔ σ ∈ alternatingGroup α := by
-- proof
  apply Equiv.Perm.isEven_iff_mem_alternatingGroup

/--
[Signs](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Signs.lean)
-/
@[path]
private lemma is_odd_iff_not_mem_alternating_group_iff
  [DecidableEq α]
  [Fintype α]
  (σ : Equiv.Perm α) :
-- imply
  σ.IsOdd ↔ σ ∉ alternatingGroup α := by
-- proof
  apply Equiv.Perm.isOdd_iff_not_mem_alternatingGroup

/--
[Signs](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Signs.lean)
-/
@[path]
private lemma is_even_one_is
  [DecidableEq α]
  [Fintype α] :
-- imply
  Equiv.Perm.IsEven (1 : Equiv.Perm α) := by
-- proof
  apply Equiv.Perm.isEven_one

/--
[Signs](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Signs.lean)
-/
@[path]
private lemma not_is_odd_one_is
  [DecidableEq α]
  [Fintype α] :
-- imply
  ¬Equiv.Perm.IsOdd (1 : Equiv.Perm α) := by
-- proof
  apply Equiv.Perm.not_isOdd_one

/--
[Signs](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Signs.lean)
-/
@[path]
private lemma is_odd_swap_is
  [DecidableEq α]
  [Fintype α]
  {x y : α}
-- given
  (hxy : x ≠ y) :
-- imply
  Equiv.Perm.IsOdd (Equiv.swap x y) := by
-- proof
  apply Equiv.Perm.isOdd_swap hxy

/--
[Signs](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Signs.lean)
-/
@[path]
private lemma is_even_or_is_odd_is
  [DecidableEq α]
  [Fintype α]
  (σ : Equiv.Perm α) :
-- imply
  σ.IsEven ∨ σ.IsOdd := by
-- proof
  apply Equiv.Perm.isEven_or_isOdd σ

/--
[Signs](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Signs.lean)
-/
@[path]
private lemma not_is_even_and_is_odd_is
  [DecidableEq α]
  [Fintype α]
  (σ : Equiv.Perm α) :
-- imply
  ¬(σ.IsEven ∧ σ.IsOdd) := by
-- proof
  apply Equiv.Perm.not_isEven_and_isOdd σ

/--
[Signs](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Signs.lean)
-/
@[path]
private lemma sign_id_eq
  [DecidableEq α]
  [Fintype α] :
-- imply
  Equiv.Perm.sign (1 : Equiv.Perm α) = 1 := by
-- proof
  apply Equiv.Perm.sign_id

/--
[Signs](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Signs.lean)
-/
@[path]
private lemma sign_transposition_eq
  [DecidableEq α]
  [Fintype α]
  {x y : α}
-- given
  (hxy : x ≠ y) :
-- imply
  Equiv.Perm.sign (Equiv.swap x y) = -1 := by
-- proof
  apply Equiv.Perm.sign_transposition hxy

/--
[Signs](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Signs.lean)
-/
@[path]
private lemma sign_is_cycle_eq
  [DecidableEq α]
  [Fintype α]
  {σ : Equiv.Perm α}
-- given
  (hσ : σ.IsCycle) :
-- imply
  Equiv.Perm.sign σ = -(-1 : ℤˣ) ^ σ.support.card := by
-- proof
  apply Equiv.Perm.sign_isCycle hσ

/--
[Signs](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Signs.lean)
-/
@[path]
private lemma sign_mul'_eq
  [DecidableEq α]
  [Fintype α]
  (σ τ : Equiv.Perm α) :
-- imply
  Equiv.Perm.sign (σ * τ) = Equiv.Perm.sign σ * Equiv.Perm.sign τ := by
-- proof
  apply Equiv.Perm.sign_mul' σ τ

/--
[Signs](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Signs.lean)
-/
@[path]
private lemma sign_prod_list_eq
  [DecidableEq α]
  [Fintype α]
  (l : List (Equiv.Perm α)) :
-- imply
  Equiv.Perm.sign l.prod = (l.map Equiv.Perm.sign).prod := by
-- proof
  apply Equiv.Perm.sign_prod_list l

/--
[Signs](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Signs.lean)
-/
@[path]
private lemma sign_inv'_eq
  [DecidableEq α]
  [Fintype α]
  (σ : Equiv.Perm α) :
-- imply
  Equiv.Perm.sign σ⁻¹ = Equiv.Perm.sign σ := by
-- proof
  apply Equiv.Perm.sign_inv' σ

/--
[Signs](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Signs.lean)
-/
@[path]
private lemma prod_diff_comp_perm_eq
  [CommRing R]
  (σ : Equiv.Perm (Fin n))
  (x : Fin n → R) :
-- imply
  ∏ i, ∏ j ∈ Finset.Ioi i, (x (σ i) - x (σ j)) =
    Equiv.Perm.sign σ * ∏ i, ∏ j ∈ Finset.Ioi i, (x i - x j) := by
-- proof
  apply Equiv.Perm.prod_diff_comp_perm σ x

/--
[Signs](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Signs.lean)
-/
@[path]
private lemma sign_eq_prod_pairs_eq
  (σ : Equiv.Perm (Fin n)) :
-- imply
  Equiv.Perm.sign σ = ∏ i, ∏ j ∈ Finset.Ioi i, (if σ i < σ j then 1 else -1) := by
-- proof
  apply Equiv.Perm.sign_eq_prod_pairs σ

/--
[Signs](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Signs.lean)
-/
@[path]
private lemma sign_hom_mul_eq
  [DecidableEq α]
  [Fintype α]
  (σ τ : Equiv.Perm α) :
-- imply
  Equiv.Perm.sign (σ * τ) = Equiv.Perm.sign σ * Equiv.Perm.sign τ := by
-- proof
  apply Equiv.Perm.sign_hom_mul σ τ

/--
[Signs](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Signs.lean)
-/
@[path]
private lemma alternating_group_is_normal_is
  [DecidableEq α]
  [Fintype α] :
-- imply
  (alternatingGroup α).Normal := by
-- proof
  apply Equiv.Perm.alternatingGroup_isNormal

/--
[Signs](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Signs.lean)
-/
@[path]
private lemma card_even_perms_eq
  [DecidableEq α]
  [Fintype α]
  [Nontrivial α] :
-- imply
  Fintype.card (alternatingGroup α) = (Fintype.card α).factorial / 2 := by
-- proof
  apply Equiv.Perm.card_even_perms

/--
[Signs](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Signs.lean)
-/
@[path]
private lemma card_odd_eq_card_even_eq
  [DecidableEq α]
  [Fintype α]
  [Nontrivial α] :
-- imply
  (Finset.univ.filter fun σ : Equiv.Perm α => Equiv.Perm.sign σ = -1).card =
    (Finset.univ.filter fun σ : Equiv.Perm α => Equiv.Perm.sign σ = 1).card := by
-- proof
  apply Equiv.Perm.card_odd_eq_card_even

/--
[Signs](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Signs.lean)
-/
@[path]
private lemma sum_sign_eq_zero_eq
  [DecidableEq α]
  [Fintype α]
  [Nontrivial α] :
-- imply
  ∑ σ : Equiv.Perm α, (Equiv.Perm.sign σ : ℤ) = 0 := by
-- proof
  apply Equiv.Perm.sum_sign_eq_zero

/--
[Signs](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Signs.lean)
-/
@[path]
private lemma sign_conj_eq_eq
  [DecidableEq α]
  [Fintype α]
  [DecidableEq β]
  [Fintype β]
  (σ : Equiv.Perm α)
  (e : α ≃ β) :
-- imply
  Equiv.Perm.sign ((e.symm.trans σ).trans e) = Equiv.Perm.sign σ := by
-- proof
  apply Equiv.Perm.sign_conj_eq σ e

/--
[Signs](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Signs.lean)
-/
@[path]
private lemma sign_id_finite_set_eq
  [DecidableEq α]
  [Fintype α] :
-- imply
  Equiv.Perm.sign (1 : Equiv.Perm α) = 1 := by
-- proof
  apply Equiv.Perm.sign_id_finiteSet

/--
[Signs](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Signs.lean)
-/
@[path]
private lemma sign_mul_finite_set_eq
  [DecidableEq α]
  [Fintype α]
  (σ τ : Equiv.Perm α) :
-- imply
  Equiv.Perm.sign (σ * τ) = Equiv.Perm.sign σ * Equiv.Perm.sign τ := by
-- proof
  apply Equiv.Perm.sign_mul_finiteSet σ τ


-- created on 2026-10-12
