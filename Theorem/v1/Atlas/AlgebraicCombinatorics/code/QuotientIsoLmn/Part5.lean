/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/QuotientIsoLmn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.AlgebraicCombinatorics.code.WreathOrbits.Part5
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.WreathOrbits
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.YoungLattice
import Instance.v1.Atlas.AlgebraicCombinatorics.code.YoungLattice.Part3
import Instance.v1.Atlas.AlgebraicCombinatorics.code.QuotientIsoLmn.Part2
set_option autoImplicit false
set_option maxHeartbeats 800000

open WreathOrbits YoungLattice YoungLattice.Lmn


namespace QuotientIsoLmn

variable {m n : ℕ}

lemma finset_filter_card_eq_sorted_filter_length
    (S : Finset (Fin m × Fin n)) (p : ℕ → Prop) [DecidablePred p] :
    (Finset.univ.filter (fun i : Fin m => p (WreathOrbits.rowSize S i))).card =
    ((WreathOrbits.sortedRowSizes S).filter (fun x => decide (p x))).length := by
  classical
  have hmulti := WreathOrbits.sortedRowSizes_multiset_eq S

  have rhs_eq : ((WreathOrbits.sortedRowSizes S).filter (fun x => decide (p x))).length =
      (Multiset.filter p (Finset.univ.val.map (WreathOrbits.rowSize S))).card := by
    rw [← hmulti]; simp [Multiset.filter_coe, Multiset.coe_card]
  rw [rhs_eq]


  have : Multiset.countP p (Finset.univ.val.map (WreathOrbits.rowSize S)) =
      (Finset.univ.filter (fun i : Fin m => p (WreathOrbits.rowSize S i))).card := by
    rw [Multiset.countP_map]; rfl
  rw [← this, Multiset.countP_eq_card_filter]

lemma card_filter_ge_of_sorted {S : Finset (Fin m × Fin n)} (k : Fin m) (v : ℕ)
    (hv : v ≤ (WreathOrbits.sortedRowSizes S).getD k.val 0) :
    k.val + 1 ≤ (Finset.univ.filter (fun i : Fin m => v ≤ WreathOrbits.rowSize S i)).card := by
  classical
  have hlen := WreathOrbits.sortedRowSizes_length S
  have hk : k.val < (WreathOrbits.sortedRowSizes S).length := by rw [hlen]; exact k.isLt
  rw [List.getD_eq_getElem _ 0 hk] at hv
  have hsorted := WreathOrbits.sortedRowSizes_pairwise S
  rw [finset_filter_card_eq_sorted_filter_length S (v ≤ ·)]

  have hge : ∀ j : ℕ, j ≤ k.val → (hj : j < (WreathOrbits.sortedRowSizes S).length) →
      v ≤ (WreathOrbits.sortedRowSizes S)[j] := by
    intro j hj hj_lt
    rcases eq_or_lt_of_le hj with rfl | hjk
    · exact hv
    · exact le_trans hv (List.pairwise_iff_getElem.mp hsorted j k.val hj_lt hk hjk)
  have htake_filter : ((WreathOrbits.sortedRowSizes S).take (k.val + 1)).filter
      (fun x => decide (v ≤ x)) = (WreathOrbits.sortedRowSizes S).take (k.val + 1) := by
    rw [List.filter_eq_self]
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
    simp only [decide_eq_true_eq]
    have hj_lt : j < k.val + 1 := by
      rwa [List.length_take, min_eq_left (by omega)] at hj
    have hj_lt_l : j < (WreathOrbits.sortedRowSizes S).length := by omega

    have heq : ((WreathOrbits.sortedRowSizes S).take (k.val + 1))[j]'hj =
        (WreathOrbits.sortedRowSizes S)[j]'hj_lt_l := List.getElem_take ..
    rw [heq]
    exact hge j (by omega) hj_lt_l
  rw [show (WreathOrbits.sortedRowSizes S).filter (fun x => decide (v ≤ x)) =
      ((WreathOrbits.sortedRowSizes S).take (k.val + 1)).filter (fun x => decide (v ≤ x)) ++
      ((WreathOrbits.sortedRowSizes S).drop (k.val + 1)).filter (fun x => decide (v ≤ x)) from by
    rw [← List.filter_append, List.take_append_drop],
    List.length_append, htake_filter, List.length_take, min_eq_left (by omega)]
  omega

lemma card_filter_ge_le_of_sorted {T : Finset (Fin m × Fin n)} (k : Fin m) (v : ℕ)
    (hv : (WreathOrbits.sortedRowSizes T).getD k.val 0 < v) :
    (Finset.univ.filter (fun i : Fin m => v ≤ WreathOrbits.rowSize T i)).card ≤ k.val := by
  classical
  have hlen := WreathOrbits.sortedRowSizes_length T
  have hk : k.val < (WreathOrbits.sortedRowSizes T).length := by rw [hlen]; exact k.isLt
  rw [List.getD_eq_getElem _ 0 hk] at hv
  have hsorted := WreathOrbits.sortedRowSizes_pairwise T
  rw [finset_filter_card_eq_sorted_filter_length T (v ≤ ·)]
  have hdrop : ((WreathOrbits.sortedRowSizes T).drop k.val).filter
      (fun x => decide (v ≤ x)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
    have hj_bound : k.val + j < (WreathOrbits.sortedRowSizes T).length := by
      rw [List.length_drop] at hj; omega
    simp only [decide_eq_true_eq]
    intro hge_contra
    have helem : (List.drop k.val (WreathOrbits.sortedRowSizes T))[j] =
        (WreathOrbits.sortedRowSizes T)[k.val + j] := List.getElem_drop ..
    rw [helem] at hge_contra
    have : (WreathOrbits.sortedRowSizes T)[k.val + j] ≤
        (WreathOrbits.sortedRowSizes T)[k.val] := by
      rcases eq_or_lt_of_le (Nat.zero_le j) with rfl | hj0
      · simp
      · exact List.pairwise_iff_getElem.mp hsorted k.val (k.val + j) hk hj_bound (by omega)
    omega
  rw [show (WreathOrbits.sortedRowSizes T).filter (fun x => decide (v ≤ x)) =
      ((WreathOrbits.sortedRowSizes T).take k.val).filter (fun x => decide (v ≤ x)) ++
      ((WreathOrbits.sortedRowSizes T).drop k.val).filter (fun x => decide (v ≤ x)) from by
    rw [← List.filter_append, List.take_append_drop],
    List.length_append, hdrop, List.length_nil, Nat.add_zero]
  exact le_trans (List.length_filter_le _ _) (by rw [List.length_take]; exact Nat.min_le_left _ _)

lemma sortedRowSizes_le_of_rowSize_le (S T : Finset (Fin m × Fin n))
    (h : ∀ i, WreathOrbits.rowSize S i ≤ WreathOrbits.rowSize T i) (k : Fin m) :
    (WreathOrbits.sortedRowSizes S).getD k.val 0 ≤
    (WreathOrbits.sortedRowSizes T).getD k.val 0 := by
  classical
  by_contra hlt
  push Not at hlt
  set v := (WreathOrbits.sortedRowSizes S).getD k.val 0
  have hcount_S := card_filter_ge_of_sorted k v (le_refl _)
  have hcount_T := card_filter_ge_le_of_sorted k v hlt
  have hsubset : (Finset.univ.filter (fun i : Fin m => v ≤ WreathOrbits.rowSize S i)) ⊆
      (Finset.univ.filter (fun i : Fin m => v ≤ WreathOrbits.rowSize T i)) := by
    intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact le_trans hi (h i)
  have := le_trans hcount_S (Finset.card_le_card hsubset)
  omega

lemma canonicalYoung_subset_of_subset {S T : Finset (Fin m × Fin n)}
    (h : S ⊆ T) : WreathOrbits.canonicalYoung S ⊆ WreathOrbits.canonicalYoung T := by
  intro ⟨i, j⟩ hmem
  rw [WreathOrbits.mem_iff_lt_rowSize (WreathOrbits.canonicalYoung_isGridYoung S).1 i j] at hmem
  rw [WreathOrbits.mem_iff_lt_rowSize (WreathOrbits.canonicalYoung_isGridYoung T).1 i j]
  calc j.val < WreathOrbits.rowSize (WreathOrbits.canonicalYoung S) i := hmem
    _ ≤ WreathOrbits.rowSize (WreathOrbits.canonicalYoung T) i := by
        rw [WreathOrbits.rowSize_canonicalYoung, WreathOrbits.rowSize_canonicalYoung]
        exact sortedRowSizes_le_of_rowSize_le S T (fun k => rowSize_le_of_subset h k) i

lemma canonicalYoung_eq_of_sameOrbit {S T : Finset (Fin m × Fin n)}
    (h : WreathOrbits.SameOrbit S T) :
    WreathOrbits.canonicalYoung S = WreathOrbits.canonicalYoung T :=
  WreathOrbits.gridYoung_unique
    (WreathOrbits.canonicalYoung_isGridYoung S)
    (WreathOrbits.canonicalYoung_isGridYoung T)
    (by rw [WreathOrbits.rowSizeMultiset_canonicalYoung, WreathOrbits.rowSizeMultiset_canonicalYoung]
        exact (WreathOrbits.sameOrbit_iff_rowSizeMultiset_eq S T).mp h)

lemma canonicalYoung_sameOrbit (S : Finset (Fin m × Fin n)) :
    WreathOrbits.SameOrbit S (WreathOrbits.canonicalYoung S) :=
  (WreathOrbits.sameOrbit_iff_rowSizeMultiset_eq S _).mpr
    (WreathOrbits.rowSizeMultiset_canonicalYoung S).symm

end QuotientIsoLmn
