/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedThreshold.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedIntegration.Part2
import Theorem.StatisticalMechanics.Code.OSSS.BetaThresholdBound
import Theorem.StatisticalMechanics.Code.OSSS.BetaCMatch.Part2
import Theorem.StatisticalMechanics.Code.OSSS.LogCesaroLimit.Part2
import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedThreshold.Part3
open scoped BigOperators Classical
open Finset Set Filter Topology
open MeasureTheory


namespace StatMech

namespace OSSS

namespace FKSharpnessWeightedThreshold

open Lattice FK

open FKSharpnessWeightedPeriodic FKSharpnessWeightedInfiniteVolume

open FKSharpnessWeightedStrict FKSharpnessWeightedIntegration

open FKSharpnessWeightedCoherentLimit

open IntegrationSubcritical BetaThresholdBound

open BetaCMatch LogCesaroLimit

def weightedSelectedPhaseHighBetaWitness
    (d : Nat) {P : Type*} [Fintype P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e) (q : Real) (hq : 0 < q)
    (beta0 : Real) : Prop :=
  exists betaStar : Real, 0 < betaStar /\ betaStar < beta0 /\
    0 < weightedSelectedPhaseSum d phaseJ hJ q hq betaStar


end FKSharpnessWeightedThreshold
end OSSS
end StatMech
