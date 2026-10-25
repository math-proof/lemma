/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TreeNoSepEuler.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.EulerComponentCount.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces.Part3
import Def.StatisticalMechanics.Code.Lattice.TreeNoSepEuler
open SimpleGraph Set

set_option linter.unusedSectionVars false


namespace StatMech

namespace Lattice

variable {V : Type*} [Finite V] [DecidableEq V]


theorem tnse_connected_deleteEdge_of_isNonBridge (A : SimpleGraph V) (hA : A.Connected)
    {e : Sym2 V} (he : tnse_IsNonBridgeEdge A e) : (A.deleteEdges {e}).Connected := by
  obtain ⟨a, b, rfl, hmem, hr⟩ := he
  exact tnse_connected_deleteEdge_of_nonbridge A hA hmem hr


end Lattice
end StatMech
