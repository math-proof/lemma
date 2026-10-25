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
open MeasureTheory
open scoped BigOperators Classical
open Set Filter Topology


namespace StatMech

namespace OSSS

namespace FKSharpnessWeightedInfiniteVolume

open Lattice FK Percolation RevealmentConstruction

open WiredBoxDifferential

open FKSharpnessWeightedPeriodic


noncomputable def weightedWiredActivePMF
    (d n : Nat) (J : Sym2 (boxVerts d n) -> Real)
    (hJ : forall e, 0 < J e) (q beta : Real)
    (hq : 0 < q) (hbeta : 0 < beta) :
    PMF (ConfigSpace (boxGraph d n).edgeSet) :=
  PMF.ofFintype
    (fun omega => ENNReal.ofReal
      (activeBCProb (boxGraph d n) (wiredBoxBoundaryGraph d n)
        (betaParams J beta) q omega)) <| by
    rw [← ENNReal.ofReal_sum_of_nonneg]
    · rw [activeBCProb_sum_eq_one (boxGraph d n)
          (wiredBoxBoundaryGraph d n) (betaParams_pos hJ hbeta)
          (betaParams_lt_one J beta) hq]
      simp
    · intro omega homega
      exact (activeBCProb_pos (boxGraph d n) (wiredBoxBoundaryGraph d n)
        (betaParams_pos hJ hbeta) (betaParams_lt_one J beta) hq omega).le


noncomputable def weightedPhaseFiniteMeasure
    (d n : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real) (a : P)
    (hJ : forall e, 0 < phaseJ a e) (q beta : Real)
    (hq : 0 < q) (hbeta : 0 < beta) :
    ProbabilityMeasure (ConfigSpace (Sym2 (Site d))) :=
  let J := phaseBoxCoupling phaseJ a n
  let hJbox : forall e, 0 < J e :=
    fun e => hJ (Sym2.map Subtype.val e)
  let mu := weightedWiredActivePMF d n J hJbox q beta hq hbeta
  ⟨mu.toMeasure.map (liftCfg (boxActiveEdge d n)),
    inferInstance⟩


noncomputable def weightedPhaseInfiniteVolume
    (d : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real) (a : P)
    (hJ : forall e, 0 < phaseJ a e) (q beta : Real)
    (hq : 0 < q) (hbeta : 0 < beta) :
    ProbabilityMeasure (ConfigSpace (Sym2 (Site d))) :=
  (prokhorov_seq_compact
    (fun n => weightedPhaseFiniteMeasure d n phaseJ a hJ q beta hq hbeta)).choose


end FKSharpnessWeightedInfiniteVolume
end OSSS
end StatMech
