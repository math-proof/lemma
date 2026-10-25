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
import Def.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedInfiniteVolume
open MeasureTheory
open scoped BigOperators Classical
open Set Filter Topology


namespace StatMech

namespace OSSS

namespace FKSharpnessWeightedInfiniteVolume

open Lattice FK Percolation RevealmentConstruction

open WiredBoxDifferential

open FKSharpnessWeightedPeriodic


theorem weightedPhaseInfiniteVolume_isLimit
    (d : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real) (a : P)
    (hJ : forall e, 0 < phaseJ a e) (q beta : Real)
    (hq : 0 < q) (hbeta : 0 < beta) :
    exists phi : Nat -> Nat, StrictMono phi ∧
      WeakConvergesTo
        (fun n => weightedPhaseFiniteMeasure d (phi n)
          phaseJ a hJ q beta hq hbeta)
        (weightedPhaseInfiniteVolume d phaseJ a hJ q beta hq hbeta) := by
  obtain ⟨phi, hphi, hlim⟩ :=
    (prokhorov_seq_compact
      (fun n => weightedPhaseFiniteMeasure d n
        phaseJ a hJ q beta hq hbeta)).choose_spec
  exact ⟨phi, hphi, hlim⟩


end FKSharpnessWeightedInfiniteVolume
end OSSS
end StatMech
