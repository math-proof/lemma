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
import Def.StatisticalMechanics.Code.Lattice.JordanBridgeCycle.Part6
open SimpleGraph Set


namespace StatMech

namespace Lattice

@[simp] theorem jbc_cyc4_adj (i j : Fin 4) : jbc_cyc4.Adj i j ↔ jbc_cyc4Rel i j := Iff.rfl

theorem jbc_csq_isSub :
    ∀ ⦃i j : Fin 4⦄, jbc_cyc4.Adj i j → (hypercubicLattice 2).Adj (jbc_csq i) (jbc_csq j) := by
  intro i j h
  rw [jbc_cyc4_adj] at h
  rw [hypercubicLattice_adj, Fin.sum_univ_two]
  revert h; fin_cases i <;> fin_cases j <;> simp [jbc_cyc4Rel, jbc_csq]


end Lattice
end StatMech
