import Mathlib
import sympy.Basic
import sympy.combinatorics.permutations.CycleDecomposition
open Equiv Equiv.Perm


/-- [CycleDecomposition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/CycleDecomposition.lean) -/
@[path]
private lemma same_cycle_iff_exists_pow_iff
-- given
  {α : Type*} [Fintype α] (f : Perm α) (i j : α) :
-- imply
  f.SameCycle i j ↔ ∃ p : ℕ, (f ^ p) i = j := by
-- proof
  apply AlgebraicCombinatorics.CycleDecomposition.sameCycle_iff_exists_pow f i j

/-- [CycleDecomposition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/CycleDecomposition.lean) -/
@[path]
private lemma same_cycle_iff_exists_pow_prime_iff
-- given
  {α : Type*} [Fintype α] (f : Perm α) (i j : α) :
-- imply
  f.SameCycle i j ↔ ∃ p : ℕ, (f ^ p) j = i := by
-- proof
  apply AlgebraicCombinatorics.CycleDecomposition.sameCycle_iff_exists_pow' f i j

/-- [CycleDecomposition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/CycleDecomposition.lean) -/
@[path]
private lemma num_cycles_total_one_eq
-- given
  {α : Type*} [DecidableEq α] [Fintype α] :
-- imply
  AlgebraicCombinatorics.CycleDecomposition.numCyclesTotal (1 : Perm α) =
    Fintype.card α := by
-- proof
  apply AlgebraicCombinatorics.CycleDecomposition.numCyclesTotal_one

/-- [CycleDecomposition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/CycleDecomposition.lean) -/
@[path]
private lemma num_cycles_one_eq
-- given
  {α : Type*} [DecidableEq α] [Fintype α] :
-- imply
  AlgebraicCombinatorics.CycleDecomposition.numCycles (1 : Perm α) = 0 := by
-- proof
  apply AlgebraicCombinatorics.CycleDecomposition.numCycles_one

/-- [CycleDecomposition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/CycleDecomposition.lean) -/
@[path]
private lemma exists_dcd_is
-- given
  {α : Type*} [DecidableEq α] [Fintype α] (σ : Perm α) :
-- imply
  ∃ (cycs : Finset (Perm α)),
    (∀ c ∈ cycs, c.IsCycle) ∧
    (cycs : Set (Perm α)).Pairwise Disjoint ∧
    ∃ h : (cycs : Set (Perm α)).Pairwise Commute, cycs.noncommProd id h = σ := by
-- proof
  apply AlgebraicCombinatorics.CycleDecomposition.exists_dcd σ

/-- [CycleDecomposition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/CycleDecomposition.lean) -/
@[path]
private lemma cycle_type_eq_iff_is_conj_iff
-- given
  {α : Type*} [DecidableEq α] [Fintype α] (σ τ : Perm α) :
-- imply
  σ.cycleType = τ.cycleType ↔ IsConj σ τ := by
-- proof
  apply AlgebraicCombinatorics.CycleDecomposition.cycleType_eq_iff_isConj σ τ

/-- [CycleDecomposition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/CycleDecomposition.lean) -/
@[path]
private lemma dcd_unique_cycle_type_eq
-- given
  {α : Type*} [DecidableEq α] [Fintype α] (σ : Perm α) :
-- imply
  ∀ (cycs : Finset (Perm α)),
    (∀ c ∈ cycs, c.IsCycle) →
    (cycs : Set (Perm α)).Pairwise Disjoint →
    (∃ h : (cycs : Set (Perm α)).Pairwise Commute, cycs.noncommProd id h = σ) →
    (cycs.val.map fun c => c.support.card) = σ.cycleType := by
-- proof
  apply AlgebraicCombinatorics.CycleDecomposition.dcd_unique_cycleType σ

/-- [CycleDecomposition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/CycleDecomposition.lean) -/
@[path]
private lemma cycles_one_eq
-- given
  {α : Type*} [DecidableEq α] [Fintype α] :
-- imply
  AlgebraicCombinatorics.CycleDecomposition.cycles (1 : Perm α) = ∅ := by
-- proof
  apply AlgebraicCombinatorics.CycleDecomposition.cycles_one

/-- [CycleDecomposition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/CycleDecomposition.lean) -/
@[path]
private lemma cycles_eq_cycle_factors_finset_eq
-- given
  {α : Type*} [DecidableEq α] [Fintype α] (σ : Perm α) :
-- imply
  AlgebraicCombinatorics.CycleDecomposition.cycles σ = σ.cycleFactorsFinset := by
-- proof
  apply AlgebraicCombinatorics.CycleDecomposition.cycles_eq_cycleFactorsFinset σ

/-- [CycleDecomposition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/CycleDecomposition.lean) -/
@[path]
private lemma mem_cycles_iff_iff
-- given
  {α : Type*} [DecidableEq α] [Fintype α] (σ c : Perm α) :
-- imply
  c ∈ AlgebraicCombinatorics.CycleDecomposition.cycles σ ↔
    c.IsCycle ∧ ∀ a ∈ c.support, c a = σ a := by
-- proof
  apply AlgebraicCombinatorics.CycleDecomposition.mem_cycles_iff σ c

/-- [CycleDecomposition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/CycleDecomposition.lean) -/
@[path]
private lemma cycles_mem_is_cycle_is
-- given
  {α : Type*} [DecidableEq α] [Fintype α] (σ c : Perm α)
    (hc : c ∈ AlgebraicCombinatorics.CycleDecomposition.cycles σ) :
-- imply
  c.IsCycle := by
-- proof
  apply AlgebraicCombinatorics.CycleDecomposition.cycles_mem_isCycle σ c hc

/-- [CycleDecomposition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/CycleDecomposition.lean) -/
@[path]
private lemma cycles_pairwise_disjoint_is
-- given
  {α : Type*} [DecidableEq α] [Fintype α] (σ : Perm α) :
-- imply
  (AlgebraicCombinatorics.CycleDecomposition.cycles σ : Set (Perm α)).Pairwise Disjoint := by
-- proof
  apply AlgebraicCombinatorics.CycleDecomposition.cycles_pairwise_disjoint σ

/-- [CycleDecomposition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/CycleDecomposition.lean) -/
@[path]
private lemma cycles_mem_commute_is
-- given
  {α : Type*} [DecidableEq α] [Fintype α] (σ : Perm α) :
-- imply
  (AlgebraicCombinatorics.CycleDecomposition.cycles σ : Set (Perm α)).Pairwise Commute := by
-- proof
  apply AlgebraicCombinatorics.CycleDecomposition.cycles_mem_commute σ

/-- [CycleDecomposition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/CycleDecomposition.lean) -/
@[path]
private lemma cycles_noncomm_prod_eq
-- given
  {α : Type*} [DecidableEq α] [Fintype α] (σ : Perm α) :
-- imply
  (AlgebraicCombinatorics.CycleDecomposition.cycles σ).noncommProd id
    (AlgebraicCombinatorics.CycleDecomposition.cycles_mem_commute σ) = σ := by
-- proof
  apply AlgebraicCombinatorics.CycleDecomposition.cycles_noncommProd_eq σ

/-- [CycleDecomposition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/CycleDecomposition.lean) -/
@[path]
private lemma cycles_support_card_ge_two
-- given
  {α : Type*} [DecidableEq α] [Fintype α] (σ c : Perm α)
    (hc : c ∈ AlgebraicCombinatorics.CycleDecomposition.cycles σ) :
-- imply
  2 ≤ c.support.card := by
-- proof
  apply AlgebraicCombinatorics.CycleDecomposition.cycles_support_card_ge_two σ c hc

/-- [CycleDecomposition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/CycleDecomposition.lean) -/
@[path]
private lemma cycles_card_eq_num_cycles_eq
-- given
  {α : Type*} [DecidableEq α] [Fintype α] (σ : Perm α) :
-- imply
  (AlgebraicCombinatorics.CycleDecomposition.cycles σ).card =
    AlgebraicCombinatorics.CycleDecomposition.numCycles σ := by
-- proof
  apply AlgebraicCombinatorics.CycleDecomposition.cycles_card_eq_numCycles σ

/-- [CycleDecomposition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/CycleDecomposition.lean) -/
@[path]
private lemma cycle_of_mem_cycles_mem
-- given
  {α : Type*} [DecidableEq α] [Fintype α] (σ : Perm α) (x : α) (hx : x ∈ σ.support) :
-- imply
  σ.cycleOf x ∈ AlgebraicCombinatorics.CycleDecomposition.cycles σ := by
-- proof
  apply AlgebraicCombinatorics.CycleDecomposition.cycleOf_mem_cycles σ x hx

/-- [CycleDecomposition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/CycleDecomposition.lean) -/
@[path]
private lemma cycle_lengths_partition_one_parts_eq
-- given
  {α : Type*} [DecidableEq α] [Fintype α] :
-- imply
  (AlgebraicCombinatorics.CycleDecomposition.cycleLengthsPartition (1 : Perm α)).parts =
    Multiset.replicate (Fintype.card α) 1 := by
-- proof
  apply AlgebraicCombinatorics.CycleDecomposition.cycleLengthsPartition_one_parts

/-- [CycleDecomposition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/CycleDecomposition.lean) -/
@[path]
private lemma cycle_lengths_one_eq
-- given
  {α : Type*} [DecidableEq α] [Fintype α] :
-- imply
  AlgebraicCombinatorics.CycleDecomposition.cycleLengths (1 : Perm α) = 0 := by
-- proof
  apply AlgebraicCombinatorics.CycleDecomposition.cycleLengths_one

/-- [CycleDecomposition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/CycleDecomposition.lean) -/
@[path]
private lemma cycle_lengths_eq_cycle_type_eq
-- given
  {α : Type*} [DecidableEq α] [Fintype α] (σ : Perm α) :
-- imply
  AlgebraicCombinatorics.CycleDecomposition.cycleLengths σ = σ.cycleType := by
-- proof
  apply AlgebraicCombinatorics.CycleDecomposition.cycleLengths_eq_cycleType σ

/-- [CycleDecomposition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/CycleDecomposition.lean) -/
@[path]
private lemma cycle_lengths_sum_eq_support_card_eq
-- given
  {α : Type*} [DecidableEq α] [Fintype α] (σ : Perm α) :
-- imply
  (AlgebraicCombinatorics.CycleDecomposition.cycleLengths σ).sum =
    σ.support.card := by
-- proof
  apply AlgebraicCombinatorics.CycleDecomposition.cycleLengths_sum_eq_support_card σ

/-- [CycleDecomposition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/CycleDecomposition.lean) -/
@[path]
private lemma cycle_lengths_card_eq_num_cycles_eq
-- given
  {α : Type*} [DecidableEq α] [Fintype α] (σ : Perm α) :
-- imply
  (AlgebraicCombinatorics.CycleDecomposition.cycleLengths σ).card =
    AlgebraicCombinatorics.CycleDecomposition.numCycles σ := by
-- proof
  apply AlgebraicCombinatorics.CycleDecomposition.cycleLengths_card_eq_numCycles σ

/-- [CycleDecomposition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/CycleDecomposition.lean) -/
@[path]
private lemma cycle_lengths_mem_ge_two
-- given
  {α : Type*} [DecidableEq α] [Fintype α] (σ : Perm α) (m : ℕ)
    (hm : m ∈ AlgebraicCombinatorics.CycleDecomposition.cycleLengths σ) :
-- imply
  2 ≤ m := by
-- proof
  apply AlgebraicCombinatorics.CycleDecomposition.cycleLengths_mem_ge_two σ m hm

/-- [CycleDecomposition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/CycleDecomposition.lean) -/
@[path]
private lemma cycle_lengths_partition_parts_eq
-- given
  {α : Type*} [DecidableEq α] [Fintype α] (σ : Perm α) :
-- imply
  (AlgebraicCombinatorics.CycleDecomposition.cycleLengthsPartition σ).parts =
    σ.cycleType + Multiset.replicate (Fintype.card α - σ.support.card) 1 := by
-- proof
  apply AlgebraicCombinatorics.CycleDecomposition.cycleLengthsPartition_parts σ

/-- [CycleDecomposition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/CycleDecomposition.lean) -/
@[path]
private lemma cycle_lengths_partition_sum_eq
-- given
  {α : Type*} [DecidableEq α] [Fintype α] (σ : Perm α) :
-- imply
  (AlgebraicCombinatorics.CycleDecomposition.cycleLengthsPartition σ).parts.sum =
    Fintype.card α := by
-- proof
  apply AlgebraicCombinatorics.CycleDecomposition.cycleLengthsPartition_sum σ

/-- [CycleDecomposition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/CycleDecomposition.lean) -/
@[path]
private lemma cyc_rotate_eq
-- given
  {α : Type*} [DecidableEq α] {l : List α} (hl : l.Nodup) (k : ℕ) :
-- imply
  l.formPerm = (l.rotate k).formPerm := by
-- proof
  apply AlgebraicCombinatorics.CycleDecomposition.cyc_rotate_eq hl k

/-- [CycleDecomposition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/CycleDecomposition.lean) -/
@[path]
private lemma cyc_eq_of_is_rotated_eq
-- given
  {α : Type*} [DecidableEq α] {l₁ l₂ : List α} (h : l₁.IsRotated l₂) (hl : l₁.Nodup) :
-- imply
  l₁.formPerm = l₂.formPerm := by
-- proof
  apply AlgebraicCombinatorics.CycleDecomposition.cyc_eq_of_isRotated h hl

/-- [CycleDecomposition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/CycleDecomposition.lean) -/
@[path]
private lemma mem_same_cycle_iff
-- given
  {α : Type*} [DecidableEq α] [Fintype α] (σ : Perm α) (i j : α) (hi : i ∈ σ.support) :
-- imply
  (∃ c ∈ AlgebraicCombinatorics.CycleDecomposition.cycles σ,
    i ∈ c.support ∧ j ∈ c.support) ↔ σ.SameCycle i j := by
-- proof
  apply AlgebraicCombinatorics.CycleDecomposition.mem_same_cycle_iff σ i j hi

/-- [CycleDecomposition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/CycleDecomposition.lean) -/
@[path]
private lemma sign_eq_neg_one_pow_card_sub_num_cycles_eq
-- given
  {n : ℕ} (σ : Perm (Fin n)) :
-- imply
  Equiv.Perm.sign σ =
    (-1 : ℤˣ) ^ (n - AlgebraicCombinatorics.CycleDecomposition.numCyclesTotal σ) := by
-- proof
  apply AlgebraicCombinatorics.CycleDecomposition.sign_eq_neg_one_pow_card_sub_numCycles σ

/-- [CycleDecomposition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/CycleDecomposition.lean) -/
@[path]
private lemma sign_eq_neg_one_pow_sum_cycle_lengths_minus_one_eq
-- given
  {n : ℕ} (σ : Perm (Fin n)) :
-- imply
  Equiv.Perm.sign σ =
    (-1 : ℤˣ) ^ (σ.cycleType.sum - σ.cycleType.card) := by
-- proof
  apply
    AlgebraicCombinatorics.CycleDecomposition.sign_eq_neg_one_pow_sum_cycle_lengths_minus_one σ

/-- [CycleDecomposition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/CycleDecomposition.lean) -/
@[path]
private lemma sign_cycle_eq
-- given
  {n : ℕ} (σ : Perm (Fin n)) (hσ : σ.IsCycle) :
-- imply
  Equiv.Perm.sign σ = (-1 : ℤˣ) ^ (σ.support.card - 1) := by
-- proof
  apply AlgebraicCombinatorics.CycleDecomposition.sign_cycle σ hσ

/-- [CycleDecomposition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/CycleDecomposition.lean) -/
@[path]
private lemma cycle_min_elem_mem_support_mem
-- given
  {α : Type*} [DecidableEq α] [Fintype α] [LinearOrder α] (c : Perm α) (hc : c.IsCycle) :
-- imply
  AlgebraicCombinatorics.CycleDecomposition.cycleMinElem c hc ∈ c.support := by
-- proof
  apply AlgebraicCombinatorics.CycleDecomposition.cycleMinElem_mem_support c hc

/-- [CycleDecomposition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/CycleDecomposition.lean) -/
@[path]
private lemma cycle_min_elem_ne_is
-- given
  {α : Type*} [DecidableEq α] [Fintype α] [LinearOrder α] (c : Perm α) (hc : c.IsCycle) :
-- imply
  c (AlgebraicCombinatorics.CycleDecomposition.cycleMinElem c hc) ≠
    AlgebraicCombinatorics.CycleDecomposition.cycleMinElem c hc := by
-- proof
  apply AlgebraicCombinatorics.CycleDecomposition.cycleMinElem_ne c hc

/-- [CycleDecomposition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/CycleDecomposition.lean) -/
@[path]
private lemma cycle_to_canonical_list_ne_nil_is
-- given
  {α : Type*} [DecidableEq α] [Fintype α] [LinearOrder α] (c : Perm α) (hc : c.IsCycle) :
-- imply
  AlgebraicCombinatorics.CycleDecomposition.cycleToCanonicalList c hc ≠ [] := by
-- proof
  apply AlgebraicCombinatorics.CycleDecomposition.cycleToCanonicalList_ne_nil c hc

/-- [CycleDecomposition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/CycleDecomposition.lean) -/
@[path]
private lemma cycle_to_canonical_list_head_eq
-- given
  {α : Type*} [DecidableEq α] [Fintype α] [LinearOrder α] (c : Perm α) (hc : c.IsCycle) :
-- imply
  (AlgebraicCombinatorics.CycleDecomposition.cycleToCanonicalList c hc).head
    (AlgebraicCombinatorics.CycleDecomposition.cycleToCanonicalList_ne_nil c hc) =
    AlgebraicCombinatorics.CycleDecomposition.cycleMinElem c hc := by
-- proof
  apply AlgebraicCombinatorics.CycleDecomposition.cycleToCanonicalList_head c hc

/-- [CycleDecomposition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/CycleDecomposition.lean) -/
@[path]
private lemma cycle_to_canonical_list_head_le
-- given
  {α : Type*} [DecidableEq α] [Fintype α] [LinearOrder α] (c : Perm α) (x : α)
    (hc : c.IsCycle)
    (hx : x ∈ AlgebraicCombinatorics.CycleDecomposition.cycleToCanonicalList c hc) :
-- imply
  (AlgebraicCombinatorics.CycleDecomposition.cycleToCanonicalList c hc).head
    (AlgebraicCombinatorics.CycleDecomposition.cycleToCanonicalList_ne_nil c hc) ≤ x := by
-- proof
  apply AlgebraicCombinatorics.CycleDecomposition.cycleToCanonicalList_head_le c hc x hx

/-- [CycleDecomposition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/CycleDecomposition.lean) -/
@[path]
private lemma cycle_to_canonical_list_form_perm_eq
-- given
  {α : Type*} [DecidableEq α] [Fintype α] [LinearOrder α] (c : Perm α) (hc : c.IsCycle) :
-- imply
  (AlgebraicCombinatorics.CycleDecomposition.cycleToCanonicalList c hc).formPerm = c := by
-- proof
  apply AlgebraicCombinatorics.CycleDecomposition.cycleToCanonicalList_formPerm c hc

/-- [CycleDecomposition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/CycleDecomposition.lean) -/
@[path]
private lemma cycle_to_canonical_list_nodup_is
-- given
  {α : Type*} [DecidableEq α] [Fintype α] [LinearOrder α] (c : Perm α) (hc : c.IsCycle) :
-- imply
  (AlgebraicCombinatorics.CycleDecomposition.cycleToCanonicalList c hc).Nodup := by
-- proof
  apply AlgebraicCombinatorics.CycleDecomposition.cycleToCanonicalList_nodup c hc

/-- [CycleDecomposition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/CycleDecomposition.lean) -/
@[path]
private lemma mem_cycle_to_canonical_list_iff
-- given
  {α : Type*} [DecidableEq α] [Fintype α] [LinearOrder α] (c : Perm α) (hc : c.IsCycle)
    (x : α) :
-- imply
  x ∈ AlgebraicCombinatorics.CycleDecomposition.cycleToCanonicalList c hc ↔
    x ∈ c.support := by
-- proof
  apply AlgebraicCombinatorics.CycleDecomposition.mem_cycleToCanonicalList_iff c hc x

/-- [CycleDecomposition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/CycleDecomposition.lean) -/
@[path]
private lemma cycle_to_canonical_list_disjoint_is
-- given
  {α : Type*} [DecidableEq α] [Fintype α] [LinearOrder α] {c d : Perm α}
    (hc : c.IsCycle) (hd : d.IsCycle) (h : Disjoint c d) :
-- imply
  List.Disjoint (AlgebraicCombinatorics.CycleDecomposition.cycleToCanonicalList c hc)
    (AlgebraicCombinatorics.CycleDecomposition.cycleToCanonicalList d hd) := by
-- proof
  apply AlgebraicCombinatorics.CycleDecomposition.cycleToCanonicalList_disjoint hc hd h

/-- [CycleDecomposition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/CycleDecomposition.lean) -/
@[path]
private lemma cycles_list_pairwise_disjoint_is
-- given
  {α : Type*} [DecidableEq α] [Fintype α] [LinearOrder α] (σ : Perm α)
    (cyclesList : List (List α))
    (hcl : cyclesList = σ.cycleFactorsFinset.toList.attach.map fun ⟨c, hc⟩ =>
      let hcycle := (mem_cycleFactorsFinset_iff.mp (Finset.mem_toList.mp hc)).1
      AlgebraicCombinatorics.CycleDecomposition.cycleToCanonicalList c hcycle) :
-- imply
  cyclesList.Pairwise List.Disjoint := by
-- proof
  apply AlgebraicCombinatorics.CycleDecomposition.cyclesList_pairwise_disjoint σ cyclesList hcl

/-- [CycleDecomposition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/CycleDecomposition.lean) -/
@[path]
private lemma cycles_list_flatten_nodup_is
-- given
  {α : Type*} [DecidableEq α] [Fintype α] [LinearOrder α] (σ : Perm α)
    (cyclesList : List (List α))
    (hcl : cyclesList = σ.cycleFactorsFinset.toList.attach.map fun ⟨c, hc⟩ =>
      let hcycle := (mem_cycleFactorsFinset_iff.mp (Finset.mem_toList.mp hc)).1
      AlgebraicCombinatorics.CycleDecomposition.cycleToCanonicalList c hcycle) :
-- imply
  cyclesList.flatten.Nodup := by
-- proof
  apply AlgebraicCombinatorics.CycleDecomposition.cyclesList_flatten_nodup σ cyclesList hcl

/-- [CycleDecomposition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/CycleDecomposition.lean) -/
@[path]
private lemma cycles_list_flatten_eq_support_iff
-- given
  {α : Type*} [DecidableEq α] [Fintype α] [LinearOrder α] (σ : Perm α)
    (cyclesList : List (List α))
    (hcl : cyclesList = σ.cycleFactorsFinset.toList.attach.map fun ⟨c, hc⟩ =>
      let hcycle := (mem_cycleFactorsFinset_iff.mp (Finset.mem_toList.mp hc)).1
      AlgebraicCombinatorics.CycleDecomposition.cycleToCanonicalList c hcycle) :
-- imply
  ∀ y : α, y ∈ cyclesList.flatten ↔ y ∈ σ.support := by
-- proof
  apply AlgebraicCombinatorics.CycleDecomposition.cyclesList_flatten_eq_support σ cyclesList hcl

/-- [CycleDecomposition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/CycleDecomposition.lean) -/
@[path]
private lemma dcd_list_to_perm_cycles_list_eq
-- given
  {α : Type*} [DecidableEq α] [Fintype α] [LinearOrder α] (σ : Perm α)
    (cyclesList : List (List α))
    (hcl : cyclesList = σ.cycleFactorsFinset.toList.attach.map fun ⟨c, hc⟩ =>
      let hcycle := (mem_cycleFactorsFinset_iff.mp (Finset.mem_toList.mp hc)).1
      AlgebraicCombinatorics.CycleDecomposition.cycleToCanonicalList c hcycle) :
-- imply
  (cyclesList.map List.formPerm).prod = σ := by
-- proof
  apply AlgebraicCombinatorics.CycleDecomposition.dcdListToPerm_cyclesList_eq σ cyclesList hcl

/-- [CycleDecomposition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/CycleDecomposition.lean) -/
@[path]
private lemma fixed_points_list_pairwise_disjoint_is
-- given
  {α : Type*} [DecidableEq α] [Fintype α] (σ : Perm α) :
-- imply
  let fixedPointsList :=
    (Finset.filter (fun x => x ∉ σ.support) Finset.univ).toList.map (fun x => [x])
  fixedPointsList.Pairwise List.Disjoint := by
-- proof
  apply AlgebraicCombinatorics.CycleDecomposition.fixedPointsList_pairwise_disjoint σ

/-- [CycleDecomposition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/CycleDecomposition.lean) -/
@[path]
private lemma singleton_disjoint_cycles_list_is
-- given
  {α : Type*} [DecidableEq α] [Fintype α] [LinearOrder α] (σ : Perm α) (x : α)
    (cyclesList : List (List α)) (hx : x ∉ σ.support)
    (hcl : cyclesList = σ.cycleFactorsFinset.toList.attach.map fun ⟨c, hc⟩ =>
      let hcycle := (mem_cycleFactorsFinset_iff.mp (Finset.mem_toList.mp hc)).1
      AlgebraicCombinatorics.CycleDecomposition.cycleToCanonicalList c hcycle) :
-- imply
  ∀ l ∈ cyclesList, List.Disjoint [x] l := by
-- proof
  apply AlgebraicCombinatorics.CycleDecomposition.singleton_disjoint_cyclesList
    σ x hx cyclesList hcl

/-- [CycleDecomposition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/CycleDecomposition.lean) -/
@[path]
private lemma canonical_dcd_exists_unique_is
-- given
  {α : Type*} [DecidableEq α] [Fintype α] [LinearOrder α] [Inhabited α] (σ : Perm α) :
-- imply
  ∃! cycleReps,
    (∀ l ∈ cycleReps, l ≠ []) ∧
    cycleReps.flatten.Nodup ∧
    (∀ x : α, x ∈ cycleReps.flatten) ∧
    (∀ l ∈ cycleReps, ∀ x ∈ l, l.head! ≤ x) ∧
    (cycleReps.Pairwise fun l1 l2 => l1.head! > l2.head!) ∧
    AlgebraicCombinatorics.CycleDecomposition.dcdListToPerm cycleReps = σ := by
-- proof
  apply AlgebraicCombinatorics.CycleDecomposition.canonicalDcd_exists_unique σ


-- created on 2026-10-11
