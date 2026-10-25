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
import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedInfiniteVolume
open MeasureTheory
open scoped BigOperators Classical
open Set Filter Topology


namespace StatMech

namespace OSSS

namespace FKSharpnessWeightedInfiniteVolume

open Lattice FK Percolation RevealmentConstruction

open WiredBoxDifferential

open FKSharpnessWeightedPeriodic


noncomputable def weightedPhaseInfiniteShell
    (d : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real) (a : P)
    (hJ : forall e, 0 < phaseJ a e) (q beta : Real)
    (hq : 0 < q) (hbeta : 0 < beta) (k : Nat) : Real :=
  ((weightedPhaseInfiniteVolume d phaseJ a hJ q beta hq hbeta :
      ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
      Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d k)


noncomputable def weightedPhaseInfiniteTheta
    (d : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real) (a : P)
    (hJ : forall e, 0 < phaseJ a e) (q beta : Real)
    (hq : 0 < q) (hbeta : 0 < beta) : Real :=
  ((weightedPhaseInfiniteVolume d phaseJ a hJ q beta hq hbeta :
      ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
      Measure (ConfigSpace (Sym2 (Site d)))).real (percolationEvent d)

end FKSharpnessWeightedInfiniteVolume
end OSSS
end StatMech
