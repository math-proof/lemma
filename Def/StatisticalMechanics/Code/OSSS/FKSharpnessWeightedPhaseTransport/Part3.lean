/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPhaseTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedCoherentLimit
import Theorem.StatisticalMechanics.Code.FK.InfiniteFiniteEnergy.Part2
import Theorem.StatisticalMechanics.Code.Percolation.GridBoxConnected.Part2
import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedPhaseTransport.Part2
open MeasureTheory
open Set


namespace StatMech

namespace OSSS

namespace FKSharpnessWeightedPhaseTransport

open Lattice FK Percolation

open FKSharpnessWeightedPeriodic

open FKSharpnessWeightedInfiniteVolume

variable {d : Nat}


def CovariantWeightedSelectedPhaseLaws
    (d : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (phase : Site d -> P) (q : Real) (hq : 0 < q) : Prop :=
  forall beta (hbeta : 0 < beta),
    CovariantWeightedPhaseCoherentFiniteEnergy d phase
      (fun a => weightedPhaseInfiniteVolume d phaseJ a (hJ a)
        q beta hq hbeta)


def CovariantWeightedSelectedPhaseTranslation
    (d : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (phase : Site d -> P) (q : Real) (hq : 0 < q) : Prop :=
  forall beta (hbeta : 0 < beta) x y,
    (weightedPhaseInfiniteVolume d phaseJ (phase y) (hJ (phase y))
        q beta hq hbeta : Measure (ConfigSpace (Sym2 (Site d)))) =
      (weightedPhaseInfiniteVolume d phaseJ (phase x) (hJ (phase x))
          q beta hq hbeta : Measure (ConfigSpace (Sym2 (Site d)))).map
        (ConfigSpace.shift (Multiplicative.ofAdd (x - y)))


def WeightedSelectedPhaseFiniteEnergy
    (d : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (q : Real) (hq : 0 < q) : Prop :=
  forall beta (hbeta : 0 < beta) a,
    HasBoxFiniteEnergy
      (weightedPhaseInfiniteVolume d phaseJ a (hJ a)
        q beta hq hbeta : Measure (ConfigSpace (Sym2 (Site d))))

end FKSharpnessWeightedPhaseTransport
end OSSS
end StatMech
