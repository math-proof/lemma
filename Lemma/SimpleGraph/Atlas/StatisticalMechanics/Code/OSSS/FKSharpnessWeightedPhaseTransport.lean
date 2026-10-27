import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedPhaseTransport.Part3
open MeasureTheory Set StatMech StatMech.OSSS StatMech.OSSS.FKSharpnessWeightedPhaseTransport


/--
[HasFiniteEnergyMerge.hasBoxFiniteEnergy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPhaseTransport.lean)
-/
@[path]
private lemma hasBoxFiniteEnergy_eq
  {d : Nat}
  {mu : Measure (ConfigSpace (Sym2 (Site d)))}
-- given
  (hfe : HasFiniteEnergyMerge mu) :
-- imply
  HasBoxFiniteEnergy mu := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPhaseTransport.HasFiniteEnergyMerge.hasBoxFiniteEnergy mu hfe

/--
[clusterInfiniteEvent_subset_forceOpen_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPhaseTransport.lean)
-/
@[path]
private lemma clusterInfiniteEvent_subset_forceOpen_preimage_eq
  {d : Nat}
  {F : Finset (Sym2 (Site d))}
  {x y : Site d}
-- given
  (hconn : forall omega, Connected d (forceOpenFinset F omega) x y) :
-- imply
  clusterInfiniteEvent d x <= forceOpenFinset F ⁻¹' clusterInfiniteEvent d y := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPhaseTransport.clusterInfiniteEvent_subset_forceOpen_preimage F x y hconn

/--
[clusterInfiniteEvent_measure_pos_of_connector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPhaseTransport.lean)
-/
@[path]
private lemma clusterInfiniteEvent_measure_pos_of_connector_eq
  {d : Nat}
  {mu : Measure (ConfigSpace (Sym2 (Site d)))}
  {F : Finset (Sym2 (Site d))}
  {x y : Site d}
-- given
  (hfe : mu.map (forceOpenFinset F) ≪ mu)
  (hconn : forall omega, Connected d (forceOpenFinset F omega) x y)
  (hx : 0 < mu (clusterInfiniteEvent d x)) :
-- imply
  0 < mu (clusterInfiniteEvent d y) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPhaseTransport.clusterInfiniteEvent_measure_pos_of_connector mu F x y hfe hconn hx

/--
[clusterInfiniteEvent_measure_pos_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPhaseTransport.lean)
-/
@[path]
private lemma clusterInfiniteEvent_measure_pos_iff_eq
  {d : Nat}
  {mu : Measure (ConfigSpace (Sym2 (Site d)))}
  {x y : Site d}
-- given
  (hfe : HasBoxFiniteEnergy mu) :
-- imply
  0 < mu (clusterInfiniteEvent d x) <-> 0 < mu (clusterInfiniteEvent d y) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPhaseTransport.clusterInfiniteEvent_measure_pos_iff mu hfe x y

/--
[clusterInfiniteEvent_real_pos_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPhaseTransport.lean)
-/
@[path]
private lemma clusterInfiniteEvent_real_pos_iff_eq
  {d : Nat}
  {mu : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsFiniteMeasure mu]
  {x y : Site d}
-- given
  (hfe : HasBoxFiniteEnergy mu) :
-- imply
  0 < mu.real (clusterInfiniteEvent d x) <-> 0 < mu.real (clusterInfiniteEvent d y) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPhaseTransport.clusterInfiniteEvent_real_pos_iff mu hfe x y

/--
[shift_mem_clusterInfiniteEvent_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPhaseTransport.lean)
-/
@[path]
private lemma shift_mem_clusterInfiniteEvent_iff_eq
  {d : Nat}
  {g : Multiplicative (Site d)}
  {omega : ConfigSpace (Sym2 (Site d))}
  {x : Site d} :
-- imply
  ConfigSpace.shift g omega ∈ clusterInfiniteEvent d (g • x) <-> omega ∈ clusterInfiniteEvent d x := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPhaseTransport.shift_mem_clusterInfiniteEvent_iff g omega x

/--
[shift_preimage_clusterInfiniteEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPhaseTransport.lean)
-/
@[path]
private lemma shift_preimage_clusterInfiniteEvent_eq
  {d : Nat}
  {g : Multiplicative (Site d)}
  {x : Site d} :
-- imply
  (ConfigSpace.shift g : ConfigSpace (Sym2 (Site d)) -> ConfigSpace (Sym2 (Site d))) ⁻¹' clusterInfiniteEvent d (g • x) = clusterInfiniteEvent d x := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPhaseTransport.shift_preimage_clusterInfiniteEvent g x

/--
[phasePositivityTransport_of_coherentFiniteEnergy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPhaseTransport.lean)
-/
@[path]
private lemma phasePositivityTransport_of_coherentFiniteEnergy_eq
  {d : Nat}
-- given
  (phase : Site d -> P)
  (hsurj : Function.Surjective phase)
  (mu : P -> ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
  (hcoh : CovariantWeightedPhaseCoherentFiniteEnergy d phase mu) :
-- imply
  WeightedPhasePositivityTransport (fun a _ => (((mu a : ProbabilityMeasure _) : Measure _).real (percolationEvent d))) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPhaseTransport.phasePositivityTransport_of_coherentFiniteEnergy phase hsurj mu hcoh

/--
[covariantWeightedSelectedPhaseLaws_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPhaseTransport.lean)
-/
@[path]
private lemma covariantWeightedSelectedPhaseLaws_iff_eq
  {d : Nat}
  {q : Real}
-- given
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall a e, 0 < phaseJ a e)
  (phase : Site d -> P)
  (hq : 0 < q) :
-- imply
  CovariantWeightedSelectedPhaseLaws d phaseJ hJ phase q hq <-> CovariantWeightedSelectedPhaseTranslation d phaseJ hJ phase q hq ∧ WeightedSelectedPhaseFiniteEnergy d phaseJ hJ q hq := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPhaseTransport.covariantWeightedSelectedPhaseLaws_iff phaseJ hJ phase q hq

/--
[covariantWeightedPhasePositivityTransport_of_selectedLaws](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPhaseTransport.lean)
-/
@[path]
private lemma covariantWeightedPhasePositivityTransport_of_selectedLaws_eq
  {d : Nat}
  {q : Real}
-- given
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall a e, 0 < phaseJ a e)
  (phase : Site d -> P)
  (hsurj : Function.Surjective phase)
  (hq : 0 < q)
  (hlaws : CovariantWeightedSelectedPhaseLaws d phaseJ hJ phase q hq) :
-- imply
  WeightedPhasePositivityTransport (weightedPhaseThetaProfile d phaseJ hJ q hq) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPhaseTransport.covariantWeightedPhasePositivityTransport_of_selectedLaws phaseJ hJ phase hsurj q hq hlaws

/--
[covariantWeightedPhasePositivityTransport_of_selectedLaws'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPhaseTransport.lean)
-/
@[path]
private lemma covariantWeightedPhasePositivityTransport_of_selectedLaws'_eq
  {d : Nat}
  {q : Real}
-- given
  (J : Sym2 (Site d) -> Real)
  (phase : Site d -> P)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall e, 0 < J e)
  (hsurj : Function.Surjective phase)
  (hcov : PhaseCovariant J phase phaseJ)
  (hq : 0 < q)
  (hlaws : CovariantWeightedSelectedPhaseLaws d phaseJ (hcov.phaseCoupling_pos hsurj hJ) phase q hq) :
-- imply
  CovariantWeightedPhasePositivityTransport d J phase phaseJ hJ hsurj hcov q hq := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPhaseTransport.covariantWeightedPhasePositivityTransport_of_selectedLaws' J phase phaseJ hJ hsurj hcov q hq hlaws

/--
[covariant_weighted_phase_common_critical_of_selectedLaws](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPhaseTransport.lean)
-/
@[path]
private lemma covariant_weighted_phase_common_critical_of_selectedLaws_eq
  {d : Nat}
  [Fintype P]
  [Nonempty P]
  {q : Real}
  {a : P}
-- given
  (J : Sym2 (Site d) -> Real)
  (phase : Site d -> P)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall e, 0 < J e)
  (hsurj : Function.Surjective phase)
  (hcov : PhaseCovariant J phase phaseJ)
  (hq : 0 < q)
  (hlaws : CovariantWeightedSelectedPhaseLaws d phaseJ (hcov.phaseCoupling_pos hsurj hJ) phase q hq) :
-- imply
  sSup {beta | Finset.univ.sup' Finset.univ_nonempty (fun b => weightedPhaseThetaProfile d phaseJ (hcov.phaseCoupling_pos hsurj hJ) q hq b beta) = 0} = sSup {beta | weightedPhaseThetaProfile d phaseJ (hcov.phaseCoupling_pos hsurj hJ) q hq a beta = 0} := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPhaseTransport.covariant_weighted_phase_common_critical_of_selectedLaws J phase phaseJ hJ hsurj hcov q hq hlaws a


-- created on 2026-10-23
