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
import Def.StatisticalMechanics.Code.Lattice.JordanBridgeCycle.Part7
open SimpleGraph Set


namespace StatMech

namespace Lattice

@[simp] theorem jbc_path3_adj (i j : Fin 4) : jbc_path3.Adj i j ↔ jbc_path3Rel i j := Iff.rfl

theorem jbc_path3_le_cyc4 : jbc_path3 ≤ jbc_cyc4 := by
  intro a b h; rw [jbc_path3_adj] at h; rw [jbc_cyc4_adj]; revert h; revert a b; decide


end Lattice
end StatMech
