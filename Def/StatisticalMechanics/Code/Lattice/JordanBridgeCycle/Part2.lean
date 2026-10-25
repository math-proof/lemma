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
import Theorem.StatisticalMechanics.Code.Lattice.JordanBridgeCycle.Part2
open SimpleGraph Set


namespace StatMech

namespace Lattice

noncomputable def jbc_rotIso (H : SimpleGraph (Site 2)) :
    jbc_latticeMinusEdges H ≃g regionGraph H where
  toEquiv := rot90Equiv
  map_rel_iff' := by
    intro a b
    rw [rot90Equiv_apply, rot90Equiv_apply, jbc_regionGraph_rot_adj]

end Lattice
end StatMech
