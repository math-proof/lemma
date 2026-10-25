/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyCorrect.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanBridgeCycle.Part10
import Def.StatisticalMechanics.Code.Lattice.WhitneyCorrect.Part3
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem whc_deleted_step_preserves (H : SimpleGraph (Site 2)) (f0 g0 : Site 2)
    (φ : Site 2 → Prop) (hcut : whc_CutColoring H f0 g0 φ) {a b : Site 2}
    (hab : ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Adj a b) : (φ a ↔ φ b) := by
  have hwr : (whb_faceRegion H).Adj a b := deleteEdges_le _ hab
  have hlat : (hypercubicLattice 2).Adj a b := ((whb_faceRegion_adj H a b).mp hwr).1
  have hnH : sharedPrimalEdge a b ∉ H.edgeSet := ((whb_faceRegion_adj H a b).mp hwr).2
  have hne : s(a, b) ≠ s(f0, g0) := by
    intro heq
    rw [deleteEdges_adj] at hab
    exact hab.2 (by rw [heq]; exact Set.mem_singleton _)
  have hnc : ¬ whc_isCross H a b := by
    rw [whc_isCross]; push Not
    refine ⟨hnH, ?_⟩
    rwa [sharedPrimalEdge_comm_of_adj hlat] at hnH
  have hkey := hcut a b hlat
  have hnflip : ¬ (whc_isCross H a b ∨ s(a, b) = s(f0, g0)) := by
    push Not; exact ⟨hnc, hne⟩
  rw [hkey] at hnflip
  by_cases ha : φ a <;> by_cases hb : φ b <;> simp_all


theorem whc_deleted_walk_preserves (H : SimpleGraph (Site 2)) (f0 g0 : Site 2)
    (φ : Site 2 → Prop) (hcut : whc_CutColoring H f0 g0 φ) {x y : Site 2}
    (w : ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Walk x y) : (φ x ↔ φ y) := by
  induction w with
  | nil => exact Iff.rfl
  | @cons a b c hab p ih => exact (whc_deleted_step_preserves H f0 g0 φ hcut hab).trans ih


theorem whc_deleted_separated (H : SimpleGraph (Site 2)) (f0 g0 : Site 2)
    (φ : Site 2 → Prop) (hcut : whc_CutColoring H f0 g0 φ) (hne : ¬ (φ f0 ↔ φ g0)) :
    ¬ ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 g0 := by
  rintro ⟨w⟩
  exact hne (whc_deleted_walk_preserves H f0 g0 φ hcut w)


end Lattice
end StatMech
