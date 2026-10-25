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
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusFreeBoundaryComparison.Part7
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising Sharpness Lattice

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


def finiteCutConditionalZ (beta : Real) (S : Finset V)
    (outside : {v : V // v ∉ S} → Bool) : Real :=
  ZJ (finiteCutGraph G S).edgeFinset (fun _ => beta)
    (fun x => beta * finiteCutBoundaryField G S outside x)


def finiteCutConditionalPairNumerator (beta : Real) (S : Finset V)
    (outside : {v : V // v ∉ S} → Bool)
    (x y : {v : V // v ∈ S}) : Real :=
  ∑ inside : ConfigSpace {v : V // v ∈ S},
    (spin inside x * spin inside y) *
      wJ (finiteCutGraph G S).edgeFinset (fun _ => beta)
        (fun z => beta * finiteCutBoundaryField G S outside z) inside

end
end StatMech.FrontierA
