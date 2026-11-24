module
public import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedCoherentLimit
public import Theorem.StatisticalMechanics.Code.FK.InfiniteFiniteEnergy.Part2
public import Theorem.StatisticalMechanics.Code.Percolation.GridBoxConnected.Part2
public import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedPhaseTransport
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


def CovariantWeightedPhaseCoherentFiniteEnergy
    (d : Nat) {P : Type*}
    (phase : Site d -> P)
    (mu : P -> ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) : Prop :=
  (forall x y,
    (mu (phase y) : Measure (ConfigSpace (Sym2 (Site d)))) =
      (mu (phase x) : Measure (ConfigSpace (Sym2 (Site d)))).map
        (ConfigSpace.shift (Multiplicative.ofAdd (x - y)) :
          ConfigSpace (Sym2 (Site d)) -> ConfigSpace (Sym2 (Site d)))) ∧
  (forall a, HasBoxFiniteEnergy
    (mu a : Measure (ConfigSpace (Sym2 (Site d)))))


end FKSharpnessWeightedPhaseTransport
end OSSS
end StatMech
