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
import Def.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedPhaseTransport.Part3
open MeasureTheory
open Set


namespace StatMech

namespace OSSS

namespace FKSharpnessWeightedPhaseTransport

open Lattice FK Percolation

open FKSharpnessWeightedPeriodic

open FKSharpnessWeightedInfiniteVolume

variable {d : Nat}


theorem covariantWeightedSelectedPhaseLaws_iff
    {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (phase : Site d -> P) (q : Real) (hq : 0 < q) :
    CovariantWeightedSelectedPhaseLaws d phaseJ hJ phase q hq <->
      CovariantWeightedSelectedPhaseTranslation d phaseJ hJ phase q hq ∧
        WeightedSelectedPhaseFiniteEnergy d phaseJ hJ q hq := by
  constructor
  · intro h
    exact ⟨fun beta hbeta => (h beta hbeta).1,
      fun beta hbeta => (h beta hbeta).2⟩
  · rintro ⟨htrans, hfe⟩ beta hbeta
    exact ⟨htrans beta hbeta, hfe beta hbeta⟩


theorem covariantWeightedPhasePositivityTransport_of_selectedLaws
    {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (phase : Site d -> P) (hsurj : Function.Surjective phase)
    (q : Real) (hq : 0 < q)
    (hlaws : CovariantWeightedSelectedPhaseLaws d phaseJ hJ phase q hq) :
    WeightedPhasePositivityTransport
      (weightedPhaseThetaProfile d phaseJ hJ q hq) := by
  intro a b beta
  unfold weightedPhaseThetaProfile
  split_ifs with hbeta
  · exact phasePositivityTransport_of_coherentFiniteEnergy phase hsurj
      (fun c => weightedPhaseInfiniteVolume d phaseJ c (hJ c)
        q beta hq hbeta)
      (hlaws beta hbeta) a b beta
  · simp


theorem covariantWeightedPhasePositivityTransport_of_selectedLaws'
    {P : Type*}
    (J : Sym2 (Site d) -> Real) (phase : Site d -> P)
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall e, 0 < J e) (hsurj : Function.Surjective phase)
    (hcov : PhaseCovariant J phase phaseJ)
    (q : Real) (hq : 0 < q)
    (hlaws : CovariantWeightedSelectedPhaseLaws d phaseJ
      (hcov.phaseCoupling_pos hsurj hJ) phase q hq) :
    CovariantWeightedPhasePositivityTransport
      d J phase phaseJ hJ hsurj hcov q hq := by
  exact covariantWeightedPhasePositivityTransport_of_selectedLaws
    phaseJ (hcov.phaseCoupling_pos hsurj hJ) phase hsurj q hq hlaws


theorem covariant_weighted_phase_common_critical_of_selectedLaws
    {P : Type*} [Fintype P] [Nonempty P]
    (J : Sym2 (Site d) -> Real) (phase : Site d -> P)
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall e, 0 < J e) (hsurj : Function.Surjective phase)
    (hcov : PhaseCovariant J phase phaseJ)
    (q : Real) (hq : 0 < q)
    (hlaws : CovariantWeightedSelectedPhaseLaws d phaseJ
      (hcov.phaseCoupling_pos hsurj hJ) phase q hq)
    (a : P) :
    sSup {beta | Finset.univ.sup' Finset.univ_nonempty
        (fun b => weightedPhaseThetaProfile d phaseJ
          (hcov.phaseCoupling_pos hsurj hJ) q hq b beta) = 0} =
      sSup {beta | weightedPhaseThetaProfile d phaseJ
        (hcov.phaseCoupling_pos hsurj hJ) q hq a beta = 0} := by
  apply covariant_weighted_phase_common_critical
    d J phase phaseJ hJ hsurj hcov q hq
  exact covariantWeightedPhasePositivityTransport_of_selectedLaws'
    J phase phaseJ hJ hsurj hcov q hq hlaws

end FKSharpnessWeightedPhaseTransport
end OSSS
end StatMech
