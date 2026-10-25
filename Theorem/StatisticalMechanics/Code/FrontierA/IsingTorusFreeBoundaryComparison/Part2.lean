/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusFreeBoundaryComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusEmbedding.Part3
import Theorem.StatisticalMechanics.Code.Ising.GinibreBoundary
import Theorem.StatisticalMechanics.Code.Ising.GHSVertexPartition.Part8
import Theorem.StatisticalMechanics.Code.Sharpness.HighTempPlusBox.Part5
import Theorem.StatisticalMechanics.Code.FrontierB.InhomogeneousFiniteVolumeRelabel.Part2
import Def.StatisticalMechanics.Code.FrontierA.IsingTorusFreeBoundaryComparison.Part2
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising Sharpness Lattice

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


@[simp] theorem finiteCutMerge_inside (S : Finset V)
    (inside : {v : V // v ∈ S} → Bool)
    (outside : {v : V // v ∉ S} → Bool) (x : {v : V // v ∈ S}) :
    finiteCutMerge S inside outside x.1 = inside x := by
  simp [finiteCutMerge, ghsvp_mergeConfig, x.2]

@[simp] theorem finiteCutMerge_outside (S : Finset V)
    (inside : {v : V // v ∈ S} → Bool)
    (outside : {v : V // v ∉ S} → Bool) (x : {v : V // v ∉ S}) :
    finiteCutMerge S inside outside x.1 = outside x := by
  simp [finiteCutMerge, ghsvp_mergeConfig, x.2]

@[simp] theorem spin_finiteCutMerge_inside (S : Finset V)
    (inside : {v : V // v ∈ S} → Bool)
    (outside : {v : V // v ∉ S} → Bool) (x : {v : V // v ∈ S}) :
    spin (finiteCutMerge S inside outside) x.1 = spin inside x := by
  unfold spin
  rw [finiteCutMerge_inside]

@[simp] theorem spin_finiteCutMerge_outside (S : Finset V)
    (inside : {v : V // v ∈ S} → Bool)
    (outside : {v : V // v ∉ S} → Bool) (x : {v : V // v ∉ S}) :
    spin (finiteCutMerge S inside outside) x.1 = spin outside x := by
  unfold spin
  rw [finiteCutMerge_outside]


end
end StatMech.FrontierA
