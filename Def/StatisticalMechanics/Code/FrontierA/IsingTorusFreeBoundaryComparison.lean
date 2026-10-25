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
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising Sharpness Lattice

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


def finiteCutBoundaryField (S : Finset V)
    (outside : {v : V // v ∉ S} → Bool) (x : {v : V // v ∈ S}) : Real :=
  ∑ y : {v : V // v ∉ S}, if G.Adj x.1 y.1 then spin outside y else 0


def finiteCutPlusBoundaryField (S : Finset V)
    (x : {v : V // v ∈ S}) : Real :=
  ∑ y : {v : V // v ∉ S}, if G.Adj x.1 y.1 then 1 else 0

end
end StatMech.FrontierA
