/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanBridgeCycle.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.JordanSeparationFinish.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerInduction.Part3
import Def.StatisticalMechanics.Code.Lattice.JordanBridgeCycle
open SimpleGraph Set


namespace StatMech

namespace Lattice

@[simp] theorem jbc_latticeMinusEdges_adj (H : SimpleGraph (Site 2)) (a b : Site 2) :
    (jbc_latticeMinusEdges H).Adj a b ↔
      (hypercubicLattice 2).Adj a b ∧ s(a, b) ∉ H.edgeSet := by
  rw [jbc_latticeMinusEdges, deleteEdges_adj]


theorem jbc_regionGraph_rot_adj (H : SimpleGraph (Site 2)) (a b : Site 2) :
    (regionGraph H).Adj (rot90Fun a) (rot90Fun b) ↔ (jbc_latticeMinusEdges H).Adj a b := by
  rw [regionGraph_adj, jbc_latticeMinusEdges_adj, rot90_adj, jbc_crossEdge_symm_rot]


end Lattice
end StatMech
