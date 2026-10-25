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
import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedThreshold
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

noncomputable def weightedNormalizedPhaseSum
    (d : Nat) {P : Type*} [Fintype P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (Jmin Jmax q beta0 : Real) (n : Nat) (beta : Real) : Real :=
  weightedPhaseSum d phaseJ q beta n /
    weightedPhaseSharpConstant d Jmin Jmax beta0

noncomputable def weightedNormalizedPhaseSumPrime
    (d : Nat) {P : Type*} [Fintype P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (Jmin Jmax q beta0 : Real) (n : Nat) (beta : Real) : Real :=
  deriv (fun b => weightedPhaseSum d phaseJ q b n) beta /
    weightedPhaseSharpConstant d Jmin Jmax beta0


noncomputable def weightedSelectedPhaseSum
    (d : Nat) {P : Type*} [Fintype P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e) (q : Real) (hq : 0 < q)
    (beta : Real) : Real :=
  ∑ a : P, weightedPhaseThetaProfile d phaseJ hJ q hq a beta

end FKSharpnessWeightedThreshold
end OSSS
end StatMech
