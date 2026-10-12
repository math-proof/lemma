import Mathlib
import sympy.Basic
import sympy.combinatorics.permutations.Signs


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
