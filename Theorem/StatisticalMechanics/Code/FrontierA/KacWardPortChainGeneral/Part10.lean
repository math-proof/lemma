/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAcyclicElimination.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStraightLineEmbedding.Part2
import Mathlib.Data.Finset.Sort
import Def.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part10
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


theorem kwOrderedSplitTransitionInBlocks_eq_fromBlocks
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (M : Matrix (kwOrderedDartPortSplitGraph G order).Dart
      (kwOrderedDartPortSplitGraph G order).Dart ℂ) :
    kwOrderedSplitTransitionInBlocks G order M = Matrix.fromBlocks
      (kwOrderedSplitTransitionInBlocks G order M).toBlocks₁₁
      (kwOrderedSplitTransitionInBlocks G order M).toBlocks₁₂
      (kwOrderedSplitTransitionInBlocks G order M).toBlocks₂₁
      (kwOrderedSplitTransitionInBlocks G order M).toBlocks₂₂ := by
  exact (Matrix.fromBlocks_toBlocks _).symm

theorem kwOrderedSplitTransitionInBlocks_det
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (M : Matrix (kwOrderedDartPortSplitGraph G order).Dart
      (kwOrderedDartPortSplitGraph G order).Dart ℂ) :
    (kwOrderedSplitTransitionInBlocks G order M).det = M.det := by
  classical
  exact Matrix.det_reindex_self
    (kwOrderedSplitDartBlockEquiv G order).symm M


theorem kw_pathGraph_edgeFinset
    (n : ℕ) :
    (SimpleGraph.pathGraph (n + 1)).edgeFinset =
      Finset.univ.image (fun i : Fin n ↦ s(i.castSucc, i.succ)) := by
  ext edge
  induction edge using Sym2.inductionOn with
  | _ u v =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        SimpleGraph.pathGraph_adj]
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Sym2.eq_iff]
      constructor
      · intro huv
        rcases huv with huv | huv
        · let i : Fin n := ⟨u.val, by omega⟩
          refine ⟨i, ?_⟩
          left
          exact ⟨Fin.ext rfl, Fin.ext huv⟩
        · let i : Fin n := ⟨v.val, by omega⟩
          refine ⟨i, ?_⟩
          right
          exact ⟨Fin.ext rfl, Fin.ext huv⟩
      · rintro ⟨i, hi⟩
        rcases hi with hi | hi
        · left
          have h₁ := congrArg Fin.val hi.1
          have h₂ := congrArg Fin.val hi.2
          simp only [Fin.val_castSucc, Fin.succ] at h₁ h₂
          omega
        · right
          have h₁ := congrArg Fin.val hi.1
          have h₂ := congrArg Fin.val hi.2
          simp only [Fin.val_castSucc, Fin.succ] at h₁ h₂
          omega

theorem kw_pathGraph_edgeFinset_card (n : ℕ) :
    (SimpleGraph.pathGraph (n + 1)).edgeFinset.card = n := by
  rw [kw_pathGraph_edgeFinset]
  rw [Finset.card_image_iff.mpr]
  · simp
  · intro i _ j _ hij
    rw [Sym2.eq_iff] at hij
    rcases hij with hij | hij
    · apply Fin.ext
      have h₁ := congrArg Fin.val hij.1
      simp only [Fin.val_castSucc] at h₁
      exact h₁
    · have h₁ := congrArg Fin.val hij.1
      have h₂ := congrArg Fin.val hij.2
      simp only [Fin.val_castSucc, Fin.succ] at h₁ h₂
      exfalso
      omega


theorem kw_pathGraph_isAcyclic (n : ℕ) :
    (SimpleGraph.pathGraph n).IsAcyclic := by
  cases n with
  | zero => exact SimpleGraph.IsAcyclic.of_subsingleton
  | succ n =>
      have htree : (SimpleGraph.pathGraph (n + 1)).IsTree := by
        rw [SimpleGraph.isTree_iff_connected_and_card]
        constructor
        · exact SimpleGraph.pathGraph_connected n
        · rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card,
            kw_pathGraph_edgeFinset_card, Nat.card_eq_fintype_card]
          simp
      exact htree.isAcyclic


end StatMech.FrontierA
