module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.EulerGeneral
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerInduction.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenClose.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenBiconditional.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.JordanFaithfulCount.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.JordanVeblenStep
public import Theorem.StatisticalMechanics.Code.Lattice.JordanVeblenPeel.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.JordanIsCyclesCount.Part5
public import Def.StatisticalMechanics.Code.Lattice.JordanGeneralCount.Part2
open SimpleGraph Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanGeneralCount.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

@[simp] theorem jgc_pend_G_adj (i j : Fin 5) : jgc_pend_G.Adj i j ↔ jgc_pend_rel i j := Iff.rfl

theorem jgc_pend_isSub : ∀ ⦃i j : Fin 5⦄, jgc_pend_G.Adj i j →
    (hypercubicLattice 2).Adj (jgc_pend_emb i) (jgc_pend_emb j) := by
  intro i j h
  rw [jgc_pend_G_adj] at h
  rw [hypercubicLattice_adj, Fin.sum_univ_two]
  revert h; fin_cases i <;> fin_cases j <;> simp [jgc_pend_rel, jgc_pend_emb]


end Lattice
end StatMech
