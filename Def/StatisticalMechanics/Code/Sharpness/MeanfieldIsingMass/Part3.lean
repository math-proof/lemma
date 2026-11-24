module
public import Theorem.StatisticalMechanics.Code.Sharpness.DeltaBound.Part2
public import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
public import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
public import Theorem.StatisticalMechanics.Code.Sharpness.WeightedFieldGhost.Part2
public import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeDomain
public import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsingMass.Part2
open Finset SimpleGraph
open scoped BigOperators symmDiff


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingMass.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
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
