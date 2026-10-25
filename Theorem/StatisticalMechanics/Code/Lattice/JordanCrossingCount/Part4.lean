/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCrossingCount.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerGeneral
import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerInduction.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenClose.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenBiconditional.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanFaithfulCount.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanVeblenStep
import Theorem.StatisticalMechanics.Code.Lattice.JordanIsCyclesCount.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanGeneralCount.Part5
import Def.StatisticalMechanics.Code.Lattice.JordanCrossingCount.Part3
open SimpleGraph Set


namespace StatMech

namespace Lattice

@[simp] theorem jcx_cross_G_adj (i j : Fin 7) : jcx_cross_G.Adj i j ↔ jcx_cross_rel i j := Iff.rfl

theorem jcx_cross_isSub : ∀ ⦃i j : Fin 7⦄, jcx_cross_G.Adj i j →
    (hypercubicLattice 2).Adj (jcx_cross_emb i) (jcx_cross_emb j) := by
  intro i j h; rw [jcx_cross_G_adj] at h
  rw [hypercubicLattice_adj, Fin.sum_univ_two]
  revert h; fin_cases i <;> fin_cases j <;> simp [jcx_cross_rel, jcx_cross_emb]


end Lattice
end StatMech
