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
import Def.StatisticalMechanics.Code.Lattice.JordanBridgeCycle.Part8
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem jbc_v0_ne_v1 : jbc_v0 ≠ jbc_v1 := by decide


theorem jbc_path3_sup_edge : jbc_path3 ⊔ edge jbc_v0 jbc_v1 = jbc_cyc4 := by
  ext i j; rw [sup_adj, jbc_path3_adj, edge_adj, jbc_cyc4_adj]; revert i j; decide


theorem jbc_path3_reach : jbc_path3.Reachable jbc_v0 jbc_v1 := by
  have a03 : jbc_path3.Adj 0 3 := by rw [jbc_path3_adj]; decide
  have a32 : jbc_path3.Adj 3 2 := by rw [jbc_path3_adj]; decide
  have a21 : jbc_path3.Adj 2 1 := by rw [jbc_path3_adj]; decide
  exact a03.reachable.trans (a32.reachable.trans a21.reachable)


end Lattice
end StatMech
