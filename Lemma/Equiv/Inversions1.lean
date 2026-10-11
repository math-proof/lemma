import Mathlib
import sympy.Basic
import sympy.combinatorics.permutations.Inversions1


/--
[Inversions1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Inversions1.lean)
-/
@[path]
private lemma perm_inv_count_le_choose_le
  (σ : Equiv.Perm (Fin n)) :
-- imply
  AlgebraicCombinatorics.Perm.invCount σ ≤ n.choose 2 := by
-- proof
  apply AlgebraicCombinatorics.Perm.invCount_le_choose σ

/--
[Inversions1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Inversions1.lean)
-/
@[path]
private lemma perm_inv_count_eq_zero_iff
  (σ : Equiv.Perm (Fin n)) :
-- imply
  AlgebraicCombinatorics.Perm.invCount σ = 0 ↔ σ = 1 := by
-- proof
  apply AlgebraicCombinatorics.Perm.invCount_eq_zero_iff σ

/--
[Inversions1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Inversions1.lean)
-/
@[path]
private lemma perm_inv_one_eq :
-- imply
  AlgebraicCombinatorics.Perm.inv (1 : Equiv.Perm (Fin n)) = ∅ := by
-- proof
  apply AlgebraicCombinatorics.Perm.inv_one

/--
[Inversions1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Inversions1.lean)
-/
@[path]
private lemma perm_inv_count_one_eq :
-- imply
  AlgebraicCombinatorics.Perm.invCount (1 : Equiv.Perm (Fin n)) = 0 := by
-- proof
  apply AlgebraicCombinatorics.Perm.invCount_one

/--
[Inversions1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Inversions1.lean)
-/
@[path]
private lemma perm_inv_count_inv_eq
  (σ : Equiv.Perm (Fin n)) :
-- imply
  AlgebraicCombinatorics.Perm.invCount σ⁻¹ = AlgebraicCombinatorics.Perm.invCount σ := by
-- proof
  apply AlgebraicCombinatorics.Perm.invCount_inv σ

/--
[Inversions1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Inversions1.lean)
-/
@[path]
private lemma perm_inv_count_mul_le
  (σ τ : Equiv.Perm (Fin n)) :
-- imply
  AlgebraicCombinatorics.Perm.invCount (σ * τ) ≤ AlgebraicCombinatorics.Perm.invCount σ + AlgebraicCombinatorics.Perm.invCount τ := by
-- proof
  apply AlgebraicCombinatorics.Perm.invCount_mul_le σ τ

/--
[Inversions1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Inversions1.lean)
-/
@[path]
private lemma perm_card_inv_count_eq_zero_eq :
-- imply
  (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => AlgebraicCombinatorics.Perm.invCount σ = 0)).card = 1 := by
-- proof
  apply AlgebraicCombinatorics.Perm.card_invCount_eq_zero

/--
[Inversions1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Inversions1.lean)
-/
@[path]
private lemma perm_longest_element_eq_rev_perm_eq :
-- imply
  AlgebraicCombinatorics.Perm.longestElement n = Fin.revPerm := by
-- proof
  apply AlgebraicCombinatorics.Perm.longestElement_eq_revPerm

/--
[Inversions1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Inversions1.lean)
-/
@[path]
private lemma perm_inv_longest_element_eq :
-- imply
  AlgebraicCombinatorics.Perm.inv (AlgebraicCombinatorics.Perm.longestElement n) = Finset.filter (fun p : Fin n × Fin n => p.1 < p.2) Finset.univ := by
-- proof
  apply AlgebraicCombinatorics.Perm.inv_longestElement

/--
[Inversions1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Inversions1.lean)
-/
@[path]
private lemma perm_inv_count_longest_element_eq :
-- imply
  AlgebraicCombinatorics.Perm.invCount (AlgebraicCombinatorics.Perm.longestElement n) = n.choose 2 := by
-- proof
  apply AlgebraicCombinatorics.Perm.invCount_longestElement

/--
[Inversions1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Inversions1.lean)
-/
@[path]
private lemma perm_inv_count_eq_choose_iff
  (σ : Equiv.Perm (Fin n)) :
-- imply
  AlgebraicCombinatorics.Perm.invCount σ = n.choose 2 ↔ σ = AlgebraicCombinatorics.Perm.longestElement n := by
-- proof
  apply AlgebraicCombinatorics.Perm.invCount_eq_choose_iff σ

/--
[Inversions1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Inversions1.lean)
-/
@[path]
private lemma perm_card_inv_count_eq_choose_eq :
-- imply
  (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => AlgebraicCombinatorics.Perm.invCount σ = n.choose 2)).card = 1 := by
-- proof
  apply AlgebraicCombinatorics.Perm.card_invCount_eq_choose

/--
[Inversions1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Inversions1.lean)
-/
@[path]
private lemma perm_card_inv_count_eq_one_eq
  (hn : 1 ≤ n) :
-- imply
  (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => AlgebraicCombinatorics.Perm.invCount σ = 1)).card = n - 1 := by
-- proof
  apply AlgebraicCombinatorics.Perm.card_invCount_eq_one hn

/--
[Inversions1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Inversions1.lean)
-/
@[path]
private lemma perm_card_inv_count_eq_two_eq
  (hn : 2 ≤ n) :
-- imply
  (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => AlgebraicCombinatorics.Perm.invCount σ = 2)).card =
  (n - 2) * (n + 1) / 2 := by
-- proof
  apply AlgebraicCombinatorics.Perm.card_invCount_eq_two hn

/--
[Inversions1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Inversions1.lean)
-/
@[path]
private lemma perm_inv_count_longest_element_mul_eq
  (σ : Equiv.Perm (Fin n)) :
-- imply
  AlgebraicCombinatorics.Perm.invCount (AlgebraicCombinatorics.Perm.longestElement n * σ) = (AlgebraicCombinatorics.Perm.nonInv σ).card := by
-- proof
  apply AlgebraicCombinatorics.Perm.invCount_longestElement_mul σ

/--
[Inversions1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Inversions1.lean)
-/
@[path]
private lemma perm_inv_count_longest_element_mul'_eq
  (σ : Equiv.Perm (Fin n)) :
-- imply
  AlgebraicCombinatorics.Perm.invCount (AlgebraicCombinatorics.Perm.longestElement n * σ) = n.choose 2 - AlgebraicCombinatorics.Perm.invCount σ := by
-- proof
  apply AlgebraicCombinatorics.Perm.invCount_longestElement_mul' σ

/--
[Inversions1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Inversions1.lean)
-/
@[path]
private lemma perm_longest_element_mul_self_eq :
-- imply
  AlgebraicCombinatorics.Perm.longestElement n * AlgebraicCombinatorics.Perm.longestElement n = 1 := by
-- proof
  apply AlgebraicCombinatorics.Perm.longestElement_mul_self

/--
[Inversions1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Inversions1.lean)
-/
@[path]
private lemma perm_longest_element_inv_eq :
-- imply
  (AlgebraicCombinatorics.Perm.longestElement n)⁻¹ = AlgebraicCombinatorics.Perm.longestElement n := by
-- proof
  apply AlgebraicCombinatorics.Perm.longestElement_inv

/--
[Inversions1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Inversions1.lean)
-/
@[path]
private lemma perm_longest_element_apply_eq
  (i : Fin n) :
-- imply
  AlgebraicCombinatorics.Perm.longestElement n i = ⟨n - 1 - i.val, by omega⟩ := by
-- proof
  apply AlgebraicCombinatorics.Perm.longestElement_apply i

/--
[Inversions1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Inversions1.lean)
-/
@[path]
private lemma perm_card_inv_count_symm_eq
  (k : ℤ) :
-- imply
  (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => (AlgebraicCombinatorics.Perm.invCount σ : ℤ) = k)).card =
  (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => (AlgebraicCombinatorics.Perm.invCount σ : ℤ) = n.choose 2 - k)).card := by
-- proof
  apply AlgebraicCombinatorics.Perm.card_invCount_symm k

/--
[Inversions1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Inversions1.lean)
-/
@[path]
private lemma perm_iic0_eq_empty_of_neg_eq
  {m : ℤ}
  (hm : m < 0) :
-- imply
  AlgebraicCombinatorics.Perm.Iic0 m = ∅ := by
-- proof
  apply AlgebraicCombinatorics.Perm.Iic0_eq_empty_of_neg hm

/--
[Inversions1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Inversions1.lean)
-/
@[path]
private lemma perm_iic0_eq_iic_of_nonneg_eq
  {m : ℤ}
  (hm : 0 ≤ m) :
-- imply
  AlgebraicCombinatorics.Perm.Iic0 m = Set.Iic m.toNat := by
-- proof
  apply AlgebraicCombinatorics.Perm.Iic0_eq_Iic_of_nonneg hm

/--
[Inversions1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Inversions1.lean)
-/
@[path]
private lemma perm_card_iic0_of_nonneg_eq
  {m : ℤ}
  (hm : 0 ≤ m) :
-- imply
  (AlgebraicCombinatorics.Perm.Iic0 m).ncard = m.toNat + 1 := by
-- proof
  apply AlgebraicCombinatorics.Perm.card_Iic0_of_nonneg hm

/--
[Inversions1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Inversions1.lean)
-/
@[path]
private lemma perm_iic0nat_eq_iic0_eq
  (m : ℕ) :
-- imply
  AlgebraicCombinatorics.Perm.Iic0Nat m = AlgebraicCombinatorics.Perm.Iic0 m := by
-- proof
  apply AlgebraicCombinatorics.Perm.Iic0Nat_eq_Iic0 m

/--
[Inversions1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Inversions1.lean)
-/
@[path]
private lemma perm_card_iic0nat_eq
  (m : ℕ) :
-- imply
  (AlgebraicCombinatorics.Perm.Iic0Nat m).ncard = m + 1 := by
-- proof
  apply AlgebraicCombinatorics.Perm.card_Iic0Nat m

/--
[Inversions1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Inversions1.lean)
-/
@[path]
private lemma perm_mem_iic0_iff
  {m : ℤ}
  {n : ℕ} :
-- imply
  n ∈ AlgebraicCombinatorics.Perm.Iic0 m ↔ (n : ℤ) ≤ m := by
-- proof
  apply AlgebraicCombinatorics.Perm.mem_Iic0_iff

/--
[Inversions1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Inversions1.lean)
-/
@[path]
private lemma perm_mem_iic0nat_iff
  {m n : ℕ} :
-- imply
  n ∈ AlgebraicCombinatorics.Perm.Iic0Nat m ↔ n ≤ m := by
-- proof
  apply AlgebraicCombinatorics.Perm.mem_Iic0Nat_iff

/--
[Inversions1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Inversions1.lean)
-/
@[path]
private lemma perm_lehmer_entry_le
  (σ : Equiv.Perm (Fin n))
  (i : Fin n) :
-- imply
  AlgebraicCombinatorics.Perm.lehmerEntry σ i ≤ n - 1 - i.val := by
-- proof
  apply AlgebraicCombinatorics.Perm.lehmerEntry_le σ i

/--
[Inversions1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Inversions1.lean)
-/
@[path]
private lemma perm_inv_count_eq_sum_lehmer_code_eq
  (σ : Equiv.Perm (Fin n)) :
-- imply
  AlgebraicCombinatorics.Perm.invCount σ = ∑ i : Fin n, AlgebraicCombinatorics.Perm.lehmerEntry σ i := by
-- proof
  apply AlgebraicCombinatorics.Perm.invCount_eq_sum_lehmerCode σ

/--
[Inversions1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Inversions1.lean)
-/
@[path]
private lemma perm_lehmer_entry_eq_filter_lt
  (σ : Equiv.Perm (Fin n))
  (i : Fin n) :
-- imply
  AlgebraicCombinatorics.Perm.lehmerEntry σ i = (Finset.filter (fun j : Fin n => i < j ∧ σ j < σ i) Finset.univ).card := by
-- proof
  apply AlgebraicCombinatorics.Perm.lehmerEntry_eq_filter_lt σ i

/--
[Inversions1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Inversions1.lean)
-/
@[path]
private lemma perm_lehmer_code_to_list_length_eq
  (σ : Equiv.Perm (Fin n)) :
-- imply
  (AlgebraicCombinatorics.Perm.lehmerCode_toList σ).length = n := by
-- proof
  apply AlgebraicCombinatorics.Perm.lehmerCode_toList_length σ

/--
[Inversions1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Inversions1.lean)
-/
@[path]
private lemma perm_lehmer_code_to_list_get_eq
  (σ : Equiv.Perm (Fin n))
  (i : Fin n) :
-- imply
  (AlgebraicCombinatorics.Perm.lehmerCode_toList σ).get ⟨i.val, by simp [AlgebraicCombinatorics.Perm.lehmerCode_toList]⟩ = AlgebraicCombinatorics.Perm.lehmerCode σ i := by
-- proof
  apply AlgebraicCombinatorics.Perm.lehmerCode_toList_get σ i

/--
[Inversions1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Inversions1.lean)
-/
@[path]
private lemma perm_lehmer_code_mem_lehmer_code_set_eq
  {n : ℕ}
  (σ : Equiv.Perm (Fin n)) :
-- imply
  AlgebraicCombinatorics.Perm.lehmerCode σ ∈ AlgebraicCombinatorics.lehmerCodeSet n := by
-- proof
  apply AlgebraicCombinatorics.Perm.lehmerCode_mem_lehmerCodeSet σ

/--
[Inversions1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Inversions1.lean)
-/
@[path]
private lemma card_lehmer_code_set_eq
  (n : ℕ) :
-- imply
  (AlgebraicCombinatorics.lehmerCodeSet n).ncard = n.factorial := by
-- proof
  apply AlgebraicCombinatorics.card_lehmerCodeSet n

/--
[Inversions1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Inversions1.lean)
-/
@[path]
private lemma perm_lehmer_code_injective_eq
  (n : ℕ) :
-- imply
  Function.Injective (fun σ : Equiv.Perm (Fin n) => AlgebraicCombinatorics.Perm.lehmerCode σ) := by
-- proof
  apply AlgebraicCombinatorics.Perm.lehmerCode_injective n

/--
[Inversions1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Inversions1.lean)
-/
@[path]
private lemma perm_lehmer_code_bijective_eq
  (n : ℕ) :
-- imply
  Function.Bijective (fun σ : Equiv.Perm (Fin n) =>
    (⟨AlgebraicCombinatorics.Perm.lehmerCode σ, AlgebraicCombinatorics.Perm.lehmerCode_mem_lehmerCodeSet σ⟩ : AlgebraicCombinatorics.lehmerCodeSet n)) := by
-- proof
  apply AlgebraicCombinatorics.Perm.lehmerCode_bijective n

/--
[Inversions1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Inversions1.lean)
-/
@[path]
private lemma lex_lt_eq_pi_lex_iff
  {n : ℕ}
  (a b : Fin n → ℤ) :
-- imply
  AlgebraicCombinatorics.lexLt a b ↔ Pi.Lex (· < ·) (fun {_} => (· < ·)) a b := by
-- proof
  apply AlgebraicCombinatorics.lexLt_eq_piLex a b

/--
[Inversions1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Inversions1.lean)
-/
@[path]
private lemma lex_lt_irrefl_eq
  {n : ℕ}
  (a : Fin n → ℤ) :
-- imply
  ¬AlgebraicCombinatorics.lexLt a a := by
-- proof
  apply AlgebraicCombinatorics.lexLt_irrefl a

/--
[Inversions1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Inversions1.lean)
-/
@[path]
private lemma lex_lt_trans_eq
  {n : ℕ}
  {a b c : Fin n → ℤ}
  (hab : AlgebraicCombinatorics.lexLt a b)
  (hbc : AlgebraicCombinatorics.lexLt b c) :
-- imply
  AlgebraicCombinatorics.lexLt a c := by
-- proof
  apply AlgebraicCombinatorics.lexLt_trans hab hbc

/--
[Inversions1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Inversions1.lean)
-/
@[path]
private lemma lex_lt_asymm_eq
  {n : ℕ}
  {a b : Fin n → ℤ}
  (hab : AlgebraicCombinatorics.lexLt a b) :
-- imply
  ¬AlgebraicCombinatorics.lexLt b a := by
-- proof
  apply AlgebraicCombinatorics.lexLt_asymm hab

/--
[Inversions1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Inversions1.lean)
-/
@[path]
private lemma lex_lt_trichotomous_eq
  {n : ℕ}
  (a b : Fin n → ℤ)
  (hab : a ≠ b) :
-- imply
  AlgebraicCombinatorics.lexLt a b ∨ AlgebraicCombinatorics.lexLt b a := by
-- proof
  apply AlgebraicCombinatorics.lexLt_trichotomous a b hab

/--
[Inversions1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Inversions1.lean)
-/
@[path]
private lemma lex_lt_strict_total_order_eq
  {n : ℕ}
  (a b : Fin n → ℤ) :
-- imply
  (a = b ∧ ¬AlgebraicCombinatorics.lexLt a b ∧ ¬AlgebraicCombinatorics.lexLt b a) ∨
  (a ≠ b ∧ AlgebraicCombinatorics.lexLt a b ∧ ¬AlgebraicCombinatorics.lexLt b a) ∨
  (a ≠ b ∧ ¬AlgebraicCombinatorics.lexLt a b ∧ AlgebraicCombinatorics.lexLt b a) := by
-- proof
  apply AlgebraicCombinatorics.lexLt_strictTotalOrder a b

/--
[Inversions1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Inversions1.lean)
-/
@[path]
private lemma perm_lehmer_code_preserves_lex_lt
  {n : ℕ}
  (σ τ : Equiv.Perm (Fin n))
  (h : AlgebraicCombinatorics.lexLt (fun i => (σ i).val) (fun i => (τ i).val)) :
-- imply
  AlgebraicCombinatorics.lexLt (fun i => (AlgebraicCombinatorics.Perm.lehmerEntry σ i : ℤ)) (fun i => (AlgebraicCombinatorics.Perm.lehmerEntry τ i : ℤ)) := by
-- proof
  apply AlgebraicCombinatorics.Perm.lehmerCode_preserves_lexLt σ τ h

/--
[Inversions1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Inversions1.lean)
-/
@[path]
private lemma perm_lehmer_entry_lt
  {n : ℕ}
  (σ : Equiv.Perm (Fin n))
  (i : Fin n) :
-- imply
  AlgebraicCombinatorics.Perm.lehmerEntry σ i < n - i.val := by
-- proof
  apply AlgebraicCombinatorics.Perm.lehmerEntry_lt σ i

/--
[Inversions1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Inversions1.lean)
-/
@[path]
private lemma length_generating_function_eq
  (n x : ℕ) :
-- imply
  ∑ σ : Equiv.Perm (Fin n), x ^ AlgebraicCombinatorics.Perm.invCount σ =
  ∏ i ∈ Finset.range n, ∑ j ∈ Finset.range (i + 1), x ^ j := by
-- proof
  apply AlgebraicCombinatorics.length_generating_function n x


-- created on 2026-10-11
