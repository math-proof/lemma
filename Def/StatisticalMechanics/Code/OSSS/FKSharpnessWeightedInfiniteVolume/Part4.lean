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
import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedInfiniteVolume.Part3
open MeasureTheory
open scoped BigOperators Classical
open Set Filter Topology


namespace StatMech

namespace OSSS

namespace FKSharpnessWeightedInfiniteVolume

open Lattice FK Percolation RevealmentConstruction

open WiredBoxDifferential

open FKSharpnessWeightedPeriodic


def WeightedPhasePositivityTransport {P : Type*}
    (thetaInf : P -> Real -> Real) : Prop :=
  forall a b beta, 0 < thetaInf a beta ↔ 0 < thetaInf b beta


noncomputable def weightedPhaseThetaProfile
    (d : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e) (q : Real) (hq : 0 < q)
    (a : P) (beta : Real) : Real :=
  if hbeta : 0 < beta then
    weightedPhaseInfiniteTheta d phaseJ a (hJ a) q beta hq hbeta
  else 0

end FKSharpnessWeightedInfiniteVolume
end OSSS
end StatMech
