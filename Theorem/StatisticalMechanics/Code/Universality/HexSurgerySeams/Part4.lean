/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSurgerySeams.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexConnEndgame
import Theorem.StatisticalMechanics.Code.Universality.HexBridge.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexInjections.Part7
import Def.StatisticalMechanics.Code.Universality.HexBridgeDecomp.Part9
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRecon.Part3
import Def.StatisticalMechanics.Code.Universality.HexSurgerySeams.Part3


namespace StatMech.Universality

open Complex HexWalk List Filter

open scoped Topology BigOperators


theorem bridgeSeqOfFinset_widths (s : Finset ℕ) (hs : ∀ T ∈ s, 0 < T) :
    (bridgeSeqOfFinset s hs).map HexBridge.width = (s.sort (· ≤ ·)).reverse := by
  unfold bridgeSeqOfFinset
  rw [List.map_pmap, List.pmap_eq_map_attach]
  simp [hexCanonBridge]


theorem hexSeams_sort_reverse_strictDecr (s : Finset ℕ) :
    ((s.sort (· ≤ ·)).reverse).Pairwise (· > ·) := by
  rw [List.pairwise_reverse]
  have hs : (s.sort (· ≤ ·)).Pairwise (· ≤ ·) := Finset.pairwise_sort s (· ≤ ·)
  have hn : (s.sort (· ≤ ·)).Nodup := Finset.sort_nodup s (· ≤ ·)
  rw [List.pairwise_iff_get] at hs ⊢
  intro i j hij
  have hle := hs i j hij
  have hne := (List.nodup_iff_injective_get.mp hn).ne (Fin.ne_of_lt hij)
  omega


theorem bridgeSeqOfFinset_strictDecr (s : Finset ℕ) (hs : ∀ T ∈ s, 0 < T) :
    StrictDecreasingWidths (bridgeSeqOfFinset s hs) := by
  unfold StrictDecreasingWidths
  rw [← List.pairwise_map (R := (· > ·)) (f := HexBridge.width), bridgeSeqOfFinset_widths]
  exact hexSeams_sort_reverse_strictDecr s


theorem bridgeSeq_prod (s : Finset ℕ) (hs : ∀ T ∈ s, 0 < T) (υ : ℕ → ℝ) :
    ((bridgeSeqOfFinset s hs).map (fun b => υ b.width)).prod = ∏ T ∈ s, υ T := by
  have hmap : (bridgeSeqOfFinset s hs).map (fun b => υ b.width)
      = ((bridgeSeqOfFinset s hs).map HexBridge.width).map υ := by
    rw [List.map_map]; rfl
  rw [hmap, bridgeSeqOfFinset_widths, List.map_reverse, List.prod_reverse,
    ← Finset.prod_map_toList s υ]
  exact (List.Perm.map υ (Finset.sort_perm_toList s (· ≤ ·))).prod_eq


end StatMech.Universality
