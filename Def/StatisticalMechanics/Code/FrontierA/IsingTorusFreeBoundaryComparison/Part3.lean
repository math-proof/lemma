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
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusFreeBoundaryComparison.Part2
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising Sharpness Lattice

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


def finiteCutInternalEdges (S : Finset V) : Finset (Sym2 V) :=
  ghsvp_vertexEdges G.edgeFinset S


def finiteCutExteriorEdges (S : Finset V) : Finset (Sym2 V) :=
  ghsvp_vertexEdges G.edgeFinset (Finset.univ \ S)


def finiteCutCrossEdges (S : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset \ (finiteCutInternalEdges G S ∪ finiteCutExteriorEdges G S)

end
end StatMech.FrontierA
