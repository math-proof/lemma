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
import Def.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedInfiniteVolume.Part2
open MeasureTheory
open scoped BigOperators Classical
open Set Filter Topology


namespace StatMech

namespace OSSS

namespace FKSharpnessWeightedInfiniteVolume

open Lattice FK Percolation RevealmentConstruction

open WiredBoxDifferential

open FKSharpnessWeightedPeriodic


theorem weightedPhaseInfiniteTheta_nonneg
    (d : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real) (a : P)
    (hJ : forall e, 0 < phaseJ a e) (q beta : Real)
    (hq : 0 < q) (hbeta : 0 < beta) :
    0 <= weightedPhaseInfiniteTheta d phaseJ a hJ q beta hq hbeta :=
  ENNReal.toReal_nonneg


theorem weightedPhaseFiniteShell_tendsto_infinite
    (d : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real) (a : P)
    (hJ : forall e, 0 < phaseJ a e) (q beta : Real)
    (hq : 0 < q) (hbeta : 0 < beta) :
    exists phi : Nat -> Nat, StrictMono phi ∧ forall k,
      Tendsto
        (fun n => ((weightedPhaseFiniteMeasure d (phi n)
          phaseJ a hJ q beta hq hbeta :
            ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
            Measure (ConfigSpace (Sym2 (Site d)))).real
              (boxBdryConnEvent d k)) atTop
        (nhds (weightedPhaseInfiniteShell d phaseJ a hJ q beta hq hbeta k)) := by
  obtain ⟨phi, hphi, hlim⟩ := weightedPhaseInfiniteVolume_isLimit
    d phaseJ a hJ q beta hq hbeta
  refine ⟨phi, hphi, fun k => ?_⟩
  exact hlim.tendsto_real_of_isClopen (isClopen_boxBdryConnEvent d k)


theorem weightedPhaseInfiniteShell_tendsto_theta
    (d : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real) (a : P)
    (hJ : forall e, 0 < phaseJ a e) (q beta : Real)
    (hq : 0 < q) (hbeta : 0 < beta) :
    Tendsto
      (weightedPhaseInfiniteShell d phaseJ a hJ q beta hq hbeta)
      atTop
      (nhds (weightedPhaseInfiniteTheta d phaseJ a hJ q beta hq hbeta)) := by
  exact boxBdryConnEvent_real_tendsto_percolation
    ((weightedPhaseInfiniteVolume d phaseJ a hJ q beta hq hbeta :
      ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
      Measure (ConfigSpace (Sym2 (Site d))))


theorem PhaseCovariant.phaseCoupling_translate
    {d : Nat} {P : Type*}
    {J : Sym2 (Site d) -> Real} {phase : Site d -> P}
    {phaseJ : P -> Sym2 (Site d) -> Real}
    (hcov : PhaseCovariant J phase phaseJ)
    (x y : Site d) (e : Sym2 (Site d)) :
    phaseJ (phase y) e =
      phaseJ (phase x) (translateAmbientEdge (y - x) e) := by
  rw [← hcov y e, ← hcov x (translateAmbientEdge (y - x) e)]
  unfold translateAmbientEdge
  rw [Sym2.map_map]
  apply congrArg J
  apply congrArg (fun f => Sym2.map f e)
  funext z
  simp [Function.comp_apply, add_assoc]


end FKSharpnessWeightedInfiniteVolume
end OSSS
end StatMech
