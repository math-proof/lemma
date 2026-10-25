/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingMass.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.DeltaBound.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Theorem.StatisticalMechanics.Code.Sharpness.WeightedFieldGhost.Part2
import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeDomain
import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsingMass.Part2
open Finset SimpleGraph
open scoped BigOperators symmDiff


namespace StatMech

namespace Sharpness

open FluxEdgeCopy

open FieldGhostDict

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


def localizedGraph (T : Finset V) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (↑(edgesIn G T) : Set (Sym2 V))


end Sharpness
end StatMech
