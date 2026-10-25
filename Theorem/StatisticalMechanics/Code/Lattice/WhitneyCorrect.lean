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
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem whc_deleted_le_latticeMinusBarrier (H : SimpleGraph (Site 2)) (f g : Site 2) :
    ((whb_faceRegion H).deleteEdges {s(f, g)}) ≤
      latticeMinusBarrier {v | ((whb_faceRegion H).deleteEdges {s(f, g)}).Reachable f v} := by
  intro x y hxy
  rw [latticeMinusBarrier_adj]
  have hwr : (whb_faceRegion H).Adj x y := deleteEdges_le _ hxy
  have hlat : (hypercubicLattice 2).Adj x y := ((whb_faceRegion_adj H x y).mp hwr).1
  refine ⟨hlat, ?_⟩
  rw [bdEdge_mk]
  intro hcon
  simp only [Set.mem_setOf_eq] at hcon
  have hr : ((whb_faceRegion H).deleteEdges {s(f, g)}).Reachable x y := hxy.reachable
  by_cases hx : ((whb_faceRegion H).deleteEdges {s(f, g)}).Reachable f x
  · exact (hcon.mp hx) (hx.trans hr)
  · exact hx (hcon.mpr (fun h => hx (h.trans hr.symm)))


end Lattice
end StatMech
