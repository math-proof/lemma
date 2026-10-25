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
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusFreeBoundaryComparison.Part5
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising Sharpness Lattice

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


def finiteCutConditionalTwoPoint (beta : Real) (S : Finset V)
    (outside : {v : V // v ∉ S} → Bool)
    (x y : {v : V // v ∈ S}) : Real :=
  expJ (finiteCutGraph G S).edgeFinset (fun _ => beta)
    (fun z => beta * finiteCutBoundaryField G S outside z)
    (fun sigma => spin sigma x * spin sigma y)


def finiteCutPlusTwoPoint (beta : Real) (S : Finset V)
    (x y : {v : V // v ∈ S}) : Real :=
  expJ (finiteCutGraph G S).edgeFinset (fun _ => beta)
    (fun z => beta * finiteCutPlusBoundaryField G S z)
    (fun sigma => spin sigma x * spin sigma y)


end
end StatMech.FrontierA
