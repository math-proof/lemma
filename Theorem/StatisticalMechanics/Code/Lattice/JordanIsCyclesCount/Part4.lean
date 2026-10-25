/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanIsCyclesCount.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerInduction.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenClose.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenBiconditional.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanFaithfulCount.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanVeblenStep
import Def.StatisticalMechanics.Code.Lattice.JordanIsCyclesCount.Part3
open SimpleGraph Set


namespace StatMech

namespace Lattice

@[simp] theorem jic_twoSq_G_adj (i j : Fin 8) : jic_twoSq_G.Adj i j ↔ jic_twoSq_rel i j := Iff.rfl

theorem jic_twoSq_isSub : ∀ ⦃i j : Fin 8⦄, jic_twoSq_G.Adj i j →
    (hypercubicLattice 2).Adj (jic_twoSq_emb i) (jic_twoSq_emb j) := by
  intro i j h
  rw [jic_twoSq_G_adj] at h
  rw [hypercubicLattice_adj, Fin.sum_univ_two]
  revert h; fin_cases i <;> fin_cases j <;> simp [jic_twoSq_rel, jic_twoSq_emb]


end Lattice
end StatMech
