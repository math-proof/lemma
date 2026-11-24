module
public import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedCoherentLimit
public import Theorem.StatisticalMechanics.Code.FK.InfiniteFiniteEnergy.Part2
public import Theorem.StatisticalMechanics.Code.Percolation.GridBoxConnected.Part2
open MeasureTheory
open Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPhaseTransport.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace OSSS

namespace FKSharpnessWeightedPhaseTransport

open Lattice FK Percolation

open FKSharpnessWeightedPeriodic

open FKSharpnessWeightedInfiniteVolume

variable {d : Nat}


def HasBoxFiniteEnergy
    (mu : Measure (ConfigSpace (Sym2 (Site d)))) : Prop :=
  forall n, mu.map (forceOpenFinset (boxEdges d n)) ≪ mu

end FKSharpnessWeightedPhaseTransport
end OSSS
end StatMech
