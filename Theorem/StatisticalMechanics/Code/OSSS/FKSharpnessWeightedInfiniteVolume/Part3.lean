/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedInfiniteVolume.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedPeriodicRepair.Part2
import Theorem.StatisticalMechanics.Code.FK.TwoPointPositiveFull
import Theorem.StatisticalMechanics.Code.Foundations.Prokhorov
import Def.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedInfiniteVolume.Part3
open MeasureTheory
open scoped BigOperators Classical
open Set Filter Topology


namespace StatMech

namespace OSSS

namespace FKSharpnessWeightedInfiniteVolume

open Lattice FK Percolation RevealmentConstruction

open WiredBoxDifferential

open FKSharpnessWeightedPeriodic


theorem weightedPhaseEnvelope_tendsto_infinite_of_diagonal
    (d : Nat) {P : Type*} [Fintype P] [Nonempty P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e) (q beta : Real)
    (hq : 0 < q) (hbeta : 0 < beta)
    (hdiag : WeightedPhaseDiagonalTailConvergence d phaseJ hJ q) :
    Tendsto
      (phaseEnvelope (fun a => weightedPhaseWiredTheta d phaseJ a q beta))
      atTop
      (nhds (Finset.univ.sup' Finset.univ_nonempty
        (fun a => weightedPhaseInfiniteTheta d phaseJ a (hJ a)
          q beta hq hbeta))) := by
  exact phaseEnvelope_tendsto _ _ (fun a => hdiag a beta hbeta hq)


end FKSharpnessWeightedInfiniteVolume
end OSSS
end StatMech
