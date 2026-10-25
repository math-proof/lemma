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
import Def.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedThreshold.Part2
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

theorem weightedSelectedPhaseSum_nonneg
    (d : Nat) {P : Type*} [Fintype P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e) (q : Real) (hq : 0 < q)
    (beta : Real) :
    0 <= weightedSelectedPhaseSum d phaseJ hJ q hq beta := by
  unfold weightedSelectedPhaseSum
  exact Finset.sum_nonneg fun a ha =>
    weightedPhaseThetaProfile_nonneg d phaseJ hJ q hq a beta


theorem weightedPhaseSum_tendsto_selectedPhaseSum
    (d : Nat) {P : Type*} [Fintype P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    Tendsto (fun n => weightedPhaseSum d phaseJ q beta n) atTop
      (nhds (weightedSelectedPhaseSum d phaseJ hJ q
        (zero_lt_one.trans_le hq) beta)) := by
  unfold weightedPhaseSum weightedSelectedPhaseSum
  simp only [weightedPhaseThetaProfile, dif_pos hbeta]
  exact tendsto_finsetSum Finset.univ fun a ha =>
    weightedPhaseProfile_tendsto_infiniteTheta
      d phaseJ a (hJ a) q beta hq hbeta


theorem weightedNormalizedPhaseSum_tendsto
    (d : Nat) {P : Type*} [Fintype P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (Jmin Jmax q beta0 beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    Tendsto
      (fun n => weightedNormalizedPhaseSum
        d phaseJ Jmin Jmax q beta0 n beta) atTop
      (nhds (weightedSelectedPhaseSum d phaseJ hJ q
        (zero_lt_one.trans_le hq) beta /
          weightedPhaseSharpConstant d Jmin Jmax beta0)) := by
  exact (weightedPhaseSum_tendsto_selectedPhaseSum
    d phaseJ hJ q beta hq hbeta).div_const _


theorem weightedNormalizedPhaseSum_meanLogTerm_tendsto
    (d : Nat) {P : Type*} [Fintype P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (Jmin Jmax q beta0 beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    Tendsto
      (fun n => Integration.meanLogTerm
        (weightedNormalizedPhaseSum d phaseJ Jmin Jmax q beta0) n beta)
      atTop
      (nhds (weightedSelectedPhaseSum d phaseJ hJ q
        (zero_lt_one.trans_le hq) beta /
          weightedPhaseSharpConstant d Jmin Jmax beta0)) := by
  exact meanLogTerm_tendsto (weightedNormalizedPhaseSum_tendsto
    d phaseJ hJ Jmin Jmax q beta0 beta hq hbeta)


end FKSharpnessWeightedThreshold
end OSSS
end StatMech
