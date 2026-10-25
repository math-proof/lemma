/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanKeepDual.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyCorrect.Part8
import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerInduction.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanFaithfulCount.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanWindingClose.Part4
import Def.StatisticalMechanics.Code.Lattice.JordanKeepDual.Part2
open SimpleGraph Set


namespace StatMech

namespace Lattice

@[simp] theorem jkd_gr9G_adj (i j : Fin 9) : jkd_gr9G.Adj i j ↔ jkd_gr9rel i j := Iff.rfl

theorem jkd_gr9_isSub : ∀ ⦃i j : Fin 9⦄, jkd_gr9G.Adj i j →
    (hypercubicLattice 2).Adj (jkd_gr9emb i) (jkd_gr9emb j) := by
  intro i j h; rw [jkd_gr9G_adj] at h
  rw [hypercubicLattice_adj, Fin.sum_univ_two]
  revert h; fin_cases i <;> fin_cases j <;> simp [jkd_gr9rel, jkd_gr9emb]


end Lattice
end StatMech
