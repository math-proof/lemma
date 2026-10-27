import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedInfiniteVolume.Part5
open MeasureTheory Set Filter Topology StatMech StatMech.OSSS StatMech.OSSS.FKSharpnessWeightedInfiniteVolume


/--
[weightedPhaseInfiniteVolume_isLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedInfiniteVolume.lean)
-/
@[path]
private lemma weightedPhaseInfiniteVolume_isLimit_eq
  {d : Nat}
  {a : P}
  {q beta : Real}
-- given
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall e, 0 < phaseJ a e)
  (hq : 0 < q)
  (hbeta : 0 < beta) :
-- imply
  exists phi : Nat -> Nat, StrictMono phi ∧ WeakConvergesTo (fun n => weightedPhaseFiniteMeasure d (phi n) phaseJ a hJ q beta hq hbeta) (weightedPhaseInfiniteVolume d phaseJ a hJ q beta hq hbeta) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedInfiniteVolume.weightedPhaseInfiniteVolume_isLimit d phaseJ a hJ q beta hq hbeta

/--
[weightedPhaseInfiniteTheta_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedInfiniteVolume.lean)
-/
@[path]
private lemma weightedPhaseInfiniteTheta_nonneg_eq
  {d : Nat}
  {a : P}
  {q beta : Real}
-- given
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall e, 0 < phaseJ a e)
  (hq : 0 < q)
  (hbeta : 0 < beta) :
-- imply
  0 <= weightedPhaseInfiniteTheta d phaseJ a hJ q beta hq hbeta := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedInfiniteVolume.weightedPhaseInfiniteTheta_nonneg d phaseJ a hJ q beta hq hbeta

/--
[weightedPhaseFiniteShell_tendsto_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedInfiniteVolume.lean)
-/
@[path]
private lemma weightedPhaseFiniteShell_tendsto_infinite_eq
  {d : Nat}
  {a : P}
  {q beta : Real}
-- given
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall e, 0 < phaseJ a e)
  (hq : 0 < q)
  (hbeta : 0 < beta) :
-- imply
  exists phi : Nat -> Nat, StrictMono phi ∧ forall k, Tendsto (fun n => ((weightedPhaseFiniteMeasure d (phi n) phaseJ a hJ q beta hq hbeta : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d k)) atTop (nhds (weightedPhaseInfiniteShell d phaseJ a hJ q beta hq hbeta k)) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedInfiniteVolume.weightedPhaseFiniteShell_tendsto_infinite d phaseJ a hJ q beta hq hbeta

/--
[weightedPhaseInfiniteShell_tendsto_theta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedInfiniteVolume.lean)
-/
@[path]
private lemma weightedPhaseInfiniteShell_tendsto_theta_eq
  {d : Nat}
  {a : P}
  {q beta : Real}
-- given
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall e, 0 < phaseJ a e)
  (hq : 0 < q)
  (hbeta : 0 < beta) :
-- imply
  Tendsto (weightedPhaseInfiniteShell d phaseJ a hJ q beta hq hbeta) atTop (nhds (weightedPhaseInfiniteTheta d phaseJ a hJ q beta hq hbeta)) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedInfiniteVolume.weightedPhaseInfiniteShell_tendsto_theta d phaseJ a hJ q beta hq hbeta

/--
[PhaseCovariant.phaseCoupling_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedInfiniteVolume.lean)
-/
@[path]
private lemma phaseCoupling_translate_eq
  {d : Nat}
  {J : Sym2 (Site d) -> Real}
  {phase : Site d -> P}
  {phaseJ : P -> Sym2 (Site d) -> Real}
  {x y : Site d}
  {e : Sym2 (Site d)}
-- given
  (hcov : PhaseCovariant J phase phaseJ) :
-- imply
  phaseJ (phase y) e = phaseJ (phase x) (translateAmbientEdge (y - x) e) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedInfiniteVolume.PhaseCovariant.phaseCoupling_translate hcov x y e

/--
[weightedPhaseEnvelope_tendsto_infinite_of_diagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedInfiniteVolume.lean)
-/
@[path]
private lemma weightedPhaseEnvelope_tendsto_infinite_of_diagonal_eq
  {d : Nat}
  [Fintype P]
  [Nonempty P]
  {q beta : Real}
-- given
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall a e, 0 < phaseJ a e)
  (hq : 0 < q)
  (hbeta : 0 < beta)
  (hdiag : WeightedPhaseDiagonalTailConvergence d phaseJ hJ q) :
-- imply
  Tendsto (phaseEnvelope (fun a => weightedPhaseWiredTheta d phaseJ a q beta)) atTop (nhds (Finset.univ.sup' Finset.univ_nonempty (fun a => weightedPhaseInfiniteTheta d phaseJ a (hJ a) q beta hq hbeta))) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedInfiniteVolume.weightedPhaseEnvelope_tendsto_infinite_of_diagonal d phaseJ hJ q beta hq hbeta hdiag

/--
[weightedPhaseThetaProfile_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedInfiniteVolume.lean)
-/
@[path]
private lemma weightedPhaseThetaProfile_nonneg_eq
  {d : Nat}
  {q : Real}
  {a : P}
  {beta : Real}
-- given
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall a e, 0 < phaseJ a e)
  (hq : 0 < q) :
-- imply
  0 <= weightedPhaseThetaProfile d phaseJ hJ q hq a beta := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedInfiniteVolume.weightedPhaseThetaProfile_nonneg d phaseJ hJ q hq a beta

/--
[phase_zeroSet_eq_of_positivityTransport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedInfiniteVolume.lean)
-/
@[path]
private lemma phase_zeroSet_eq_of_positivityTransport_eq
  {a b : P}
-- given
  (thetaInf : P -> Real -> Real)
  (hnonneg : forall a beta, 0 <= thetaInf a beta)
  (htransport : WeightedPhasePositivityTransport thetaInf) :
-- imply
  {beta | thetaInf a beta = 0} = {beta | thetaInf b beta = 0} := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedInfiniteVolume.phase_zeroSet_eq_of_positivityTransport thetaInf hnonneg htransport a b

/--
[phase_critical_eq_of_positivityTransport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedInfiniteVolume.lean)
-/
@[path]
private lemma phase_critical_eq_of_positivityTransport_eq
  {a b : P}
-- given
  (thetaInf : P -> Real -> Real)
  (hnonneg : forall a beta, 0 <= thetaInf a beta)
  (htransport : WeightedPhasePositivityTransport thetaInf) :
-- imply
  sSup {beta | thetaInf a beta = 0} = sSup {beta | thetaInf b beta = 0} := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedInfiniteVolume.phase_critical_eq_of_positivityTransport thetaInf hnonneg htransport a b

/--
[phaseEnvelope_zeroSet_eq_phase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedInfiniteVolume.lean)
-/
@[path]
private lemma phaseEnvelope_zeroSet_eq_phase_eq
  [Fintype P]
  [Nonempty P]
  {a : P}
-- given
  (thetaInf : P -> Real -> Real)
  (hnonneg : forall a beta, 0 <= thetaInf a beta)
  (htransport : WeightedPhasePositivityTransport thetaInf) :
-- imply
  {beta | Finset.univ.sup' Finset.univ_nonempty (fun b => thetaInf b beta) = 0} = {beta | thetaInf a beta = 0} := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedInfiniteVolume.phaseEnvelope_zeroSet_eq_phase thetaInf hnonneg htransport a

/--
[phaseEnvelope_critical_eq_phase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedInfiniteVolume.lean)
-/
@[path]
private lemma phaseEnvelope_critical_eq_phase_eq
  [Fintype P]
  [Nonempty P]
  {a : P}
-- given
  (thetaInf : P -> Real -> Real)
  (hnonneg : forall a beta, 0 <= thetaInf a beta)
  (htransport : WeightedPhasePositivityTransport thetaInf) :
-- imply
  sSup {beta | Finset.univ.sup' Finset.univ_nonempty (fun b => thetaInf b beta) = 0} = sSup {beta | thetaInf a beta = 0} := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedInfiniteVolume.phaseEnvelope_critical_eq_phase thetaInf hnonneg htransport a

/--
[covariant_weighted_phase_common_critical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedInfiniteVolume.lean)
-/
@[path]
private lemma covariant_weighted_phase_common_critical_eq
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
  (htransport : CovariantWeightedPhasePositivityTransport d J phase phaseJ hJ hsurj hcov q hq) :
-- imply
  sSup {beta | Finset.univ.sup' Finset.univ_nonempty (fun b => weightedPhaseThetaProfile d phaseJ (hcov.phaseCoupling_pos hsurj hJ) q hq b beta) = 0} = sSup {beta | weightedPhaseThetaProfile d phaseJ (hcov.phaseCoupling_pos hsurj hJ) q hq a beta = 0} := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedInfiniteVolume.covariant_weighted_phase_common_critical d J phase phaseJ hJ hsurj hcov q hq htransport a


-- created on 2026-10-23
