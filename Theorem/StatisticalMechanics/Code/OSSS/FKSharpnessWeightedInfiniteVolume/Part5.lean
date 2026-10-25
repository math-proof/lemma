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
import Def.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedInfiniteVolume.Part5
open MeasureTheory
open scoped BigOperators Classical
open Set Filter Topology


namespace StatMech

namespace OSSS

namespace FKSharpnessWeightedInfiniteVolume

open Lattice FK Percolation RevealmentConstruction

open WiredBoxDifferential

open FKSharpnessWeightedPeriodic


theorem phase_zeroSet_eq_of_positivityTransport
    {P : Type*} (thetaInf : P -> Real -> Real)
    (hnonneg : forall a beta, 0 <= thetaInf a beta)
    (htransport : WeightedPhasePositivityTransport thetaInf)
    (a b : P) :
    {beta | thetaInf a beta = 0} = {beta | thetaInf b beta = 0} := by
  ext beta
  constructor
  · intro ha
    change thetaInf a beta = 0 at ha
    apply le_antisymm
    · apply le_of_not_gt
      intro hbpos
      have hapos := (htransport b a beta).mp hbpos
      linarith
    · exact hnonneg b beta
  · intro hb
    change thetaInf b beta = 0 at hb
    apply le_antisymm
    · apply le_of_not_gt
      intro hapos
      have hbpos := (htransport a b beta).mp hapos
      linarith
    · exact hnonneg a beta


theorem phase_critical_eq_of_positivityTransport
    {P : Type*} (thetaInf : P -> Real -> Real)
    (hnonneg : forall a beta, 0 <= thetaInf a beta)
    (htransport : WeightedPhasePositivityTransport thetaInf)
    (a b : P) :
    sSup {beta | thetaInf a beta = 0} =
      sSup {beta | thetaInf b beta = 0} := by
  rw [phase_zeroSet_eq_of_positivityTransport thetaInf hnonneg htransport a b]


theorem phaseEnvelope_zeroSet_eq_phase
    {P : Type*} [Fintype P] [Nonempty P]
    (thetaInf : P -> Real -> Real)
    (hnonneg : forall a beta, 0 <= thetaInf a beta)
    (htransport : WeightedPhasePositivityTransport thetaInf)
    (a : P) :
    {beta | Finset.univ.sup' Finset.univ_nonempty
        (fun b => thetaInf b beta) = 0} =
      {beta | thetaInf a beta = 0} := by
  ext beta
  constructor
  · intro hsup
    apply le_antisymm
    · exact (Finset.le_sup' (fun b => thetaInf b beta)
        (Finset.mem_univ a)).trans_eq hsup
    · exact hnonneg a beta
  · intro ha
    apply le_antisymm
    · apply Finset.sup'_le Finset.univ_nonempty
      intro b hb
      have hz := Set.ext_iff.mp
        (phase_zeroSet_eq_of_positivityTransport thetaInf hnonneg htransport b a) beta
      exact le_of_eq (hz.mpr ha)
    · exact (hnonneg a beta).trans
        (Finset.le_sup' (fun b => thetaInf b beta) (Finset.mem_univ a))


theorem phaseEnvelope_critical_eq_phase
    {P : Type*} [Fintype P] [Nonempty P]
    (thetaInf : P -> Real -> Real)
    (hnonneg : forall a beta, 0 <= thetaInf a beta)
    (htransport : WeightedPhasePositivityTransport thetaInf)
    (a : P) :
    sSup {beta | Finset.univ.sup' Finset.univ_nonempty
        (fun b => thetaInf b beta) = 0} =
      sSup {beta | thetaInf a beta = 0} := by
  rw [phaseEnvelope_zeroSet_eq_phase thetaInf hnonneg htransport a]


theorem covariant_weighted_phase_common_critical
    (d : Nat) {P : Type*} [Fintype P] [Nonempty P]
    (J : Sym2 (Site d) -> Real) (phase : Site d -> P)
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall e, 0 < J e) (hsurj : Function.Surjective phase)
    (hcov : PhaseCovariant J phase phaseJ)
    (q : Real) (hq : 0 < q)
    (htransport : CovariantWeightedPhasePositivityTransport
      d J phase phaseJ hJ hsurj hcov q hq)
    (a : P) :
    sSup {beta | Finset.univ.sup' Finset.univ_nonempty
        (fun b => weightedPhaseThetaProfile d phaseJ
          (hcov.phaseCoupling_pos hsurj hJ) q hq b beta) = 0} =
      sSup {beta | weightedPhaseThetaProfile d phaseJ
        (hcov.phaseCoupling_pos hsurj hJ) q hq a beta = 0} := by
  apply phaseEnvelope_critical_eq_phase
  · exact weightedPhaseThetaProfile_nonneg d phaseJ
      (hcov.phaseCoupling_pos hsurj hJ) q hq
  · exact htransport

end FKSharpnessWeightedInfiniteVolume
end OSSS
end StatMech
