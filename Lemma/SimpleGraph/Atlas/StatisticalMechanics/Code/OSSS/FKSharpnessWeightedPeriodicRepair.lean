import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedPeriodicRepair.Part2
open Finset Set StatMech StatMech.OSSS StatMech.OSSS.FKSharpnessWeightedPeriodicRepair


/--
[edgeProductW_reCfgIso](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPeriodicRepair.lean)
-/
@[path]
private lemma edgeProductW_reCfgIso_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  {sigma : V ≃ W}
  {omega : ConfigSpace (Sym2 W)}
-- given
  (hsigma : forall x y, G.Adj x y ↔ H.Adj (sigma x) (sigma y))
  (pfV : Sym2 V -> Real)
  (pfW : Sym2 W -> Real)
  (hpf : forall e, pfW (Sym2.map sigma e) = pfV e) :
-- imply
  edgeProductW G pfV (reCfgIso sigma omega) = edgeProductW H pfW omega := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPeriodicRepair.edgeProductW_reCfgIso G H sigma hsigma pfV pfW hpf omega

/--
[bcWeightW_boundaryClique_reCfgIso](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPeriodicRepair.lean)
-/
@[path]
private lemma bcWeightW_boundaryClique_reCfgIso_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  [DecidablePred bdryV]
  [DecidablePred bdryW]
  {sigma : V ≃ W}
  {q : Real}
  {omega : ConfigSpace (Sym2 W)}
-- given
  (bdryV : V -> Prop)
  (bdryW : W -> Prop)
  (hsigma : forall x y, G.Adj x y ↔ H.Adj (sigma x) (sigma y))
  (hbdry : forall x, bdryV x ↔ bdryW (sigma x))
  (pfV : Sym2 V -> Real)
  (pfW : Sym2 W -> Real)
  (hpf : forall e, pfW (Sym2.map sigma e) = pfV e) :
-- imply
  bcWeightW G (boundaryCliqueGraph bdryV) pfV q (reCfgIso sigma omega) = bcWeightW H (boundaryCliqueGraph bdryW) pfW q omega := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPeriodicRepair.bcWeightW_boundaryClique_reCfgIso G H bdryV bdryW sigma hsigma hbdry pfV pfW hpf q omega

/--
[bcProbW_boundaryClique_reCfgIso](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPeriodicRepair.lean)
-/
@[path]
private lemma bcProbW_boundaryClique_reCfgIso_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  [DecidablePred bdryV]
  [DecidablePred bdryW]
  {sigma : V ≃ W}
  {q : Real}
  {omega : ConfigSpace (Sym2 W)}
-- given
  (bdryV : V -> Prop)
  (bdryW : W -> Prop)
  (hsigma : forall x y, G.Adj x y ↔ H.Adj (sigma x) (sigma y))
  (hbdry : forall x, bdryV x ↔ bdryW (sigma x))
  (pfV : Sym2 V -> Real)
  (pfW : Sym2 W -> Real)
  (hpf : forall e, pfW (Sym2.map sigma e) = pfV e) :
-- imply
  bcProbW G (boundaryCliqueGraph bdryV) pfV q (reCfgIso sigma omega) = bcProbW H (boundaryCliqueGraph bdryW) pfW q omega := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPeriodicRepair.bcProbW_boundaryClique_reCfgIso G H bdryV bdryW sigma hsigma hbdry pfV pfW hpf q omega

/--
[weighted_transShellEvent_mass_eq_phase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPeriodicRepair.lean)
-/
@[path]
private lemma weighted_transShellEvent_mass_eq_phase_eq
  {d k : Nat}
  {x : Site d}
  {q beta : Real}
-- given
  (J : Sym2 (Site d) -> Real)
  (phase : Site d -> P)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hcov : PhaseCovariant J phase phaseJ) :
-- imply
  (∑ eta, (transShellEvent d k x).indicator (fun _ => (1 : Real)) eta * bcProbW (fvs_transBoxGraph d (2 * k) x) (boundaryCliqueGraph (fvs_transBoxBoundary d (2 * k) x)) (betaParams (transBoxCoupling J (2 * k) x) beta) q eta) = ∑ rho, (centeredShellEvent d k).indicator (fun _ => (1 : Real)) rho * bcProbW (boxGraph d (2 * k)) (boundaryCliqueGraph (boxBoundary d (2 * k))) (betaParams (phaseBoxCoupling phaseJ (phase x) (2 * k)) beta) q rho := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPeriodicRepair.weighted_transShellEvent_mass_eq_phase d k J phase phaseJ hcov x q beta

/--
[weightedPhaseWiredTheta_eq_centeredShellMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPeriodicRepair.lean)
-/
@[path]
private lemma weightedPhaseWiredTheta_eq_centeredShellMass_eq
  {d k : Nat}
  {a : P}
  {q beta : Real}
-- given
  (hk : 1 <= k)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall e, 0 < phaseJ a e)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  weightedPhaseWiredTheta d phaseJ a q beta k = ∑ rho, (centeredShellEvent d k).indicator (fun _ => (1 : Real)) rho * bcProbW (boxGraph d (2 * k)) (boundaryCliqueGraph (boxBoundary d (2 * k))) (betaParams (phaseBoxCoupling phaseJ a (2 * k)) beta) q rho := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPeriodicRepair.weightedPhaseWiredTheta_eq_centeredShellMass d k hk phaseJ a hJ q beta hq hbeta

/--
[weightedOuterInnerConn_le_transShellMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPeriodicRepair.lean)
-/
@[path]
private lemma weightedOuterInnerConn_le_transShellMass_eq
  {d n k : Nat}
  {x : Site d}
  {q beta : Real}
-- given
  (J : Sym2 (Site d) -> Real)
  (hJ : forall e, 0 < J e)
  (hq : 1 <= q)
  (hbeta : 0 < beta)
  (hsub : fvs_transBox d (2 * k) x ⊆ box d (2 * n)) :
-- imply
  weightedOuterInnerConn d n J q beta x k <= ∑ rho, (ocd_innerRestrict (flc_incl hsub) ⁻¹' transShellEvent d k x).indicator (fun _ => (1 : Real)) rho * bcProbW (boxGraph d (2 * n)) (boundaryCliqueGraph (boxBoundary d (2 * n))) (betaParams (boxCoupling J (2 * n)) beta) q rho := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPeriodicRepair.weightedOuterInnerConn_le_transShellMass d n k x J hJ q beta hq hbeta hsub

/--
[weightedOuterInnerConn_le_phase_strict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPeriodicRepair.lean)
-/
@[path]
private lemma weightedOuterInnerConn_le_phase_strict_eq
  {d n k : Nat}
  {x : Site d}
  {q beta : Real}
-- given
  (hx : x ∈ box d n)
  (hk : 1 <= k)
  (hkn : 2 * k < n)
  (J : Sym2 (Site d) -> Real)
  (hJ : forall e, 0 < J e)
  (phase : Site d -> P)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hcov : PhaseCovariant J phase phaseJ)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  weightedOuterInnerConn d n J q beta x k <= weightedPhaseWiredTheta d phaseJ (phase x) q beta k := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPeriodicRepair.weightedOuterInnerConn_le_phase_strict d n k x hx hk hkn J hJ phase phaseJ hcov q beta hq hbeta

/--
[weightedPhaseOffCentreStrict_of_covariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPeriodicRepair.lean)
-/
@[path]
private lemma weightedPhaseOffCentreStrict_of_covariant_eq
  {d n : Nat}
  {q beta : Real}
-- given
  (J : Sym2 (Site d) -> Real)
  (hJ : forall e, 0 < J e)
  (phase : Site d -> P)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hcov : PhaseCovariant J phase phaseJ)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  WeightedPhaseOffCentreStrict d n J phase (fun a => weightedPhaseWiredTheta d phaseJ a q beta) q beta := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPeriodicRepair.weightedPhaseOffCentreStrict_of_covariant d n J hJ phase phaseJ hcov q beta hq hbeta

/--
[periodicWeightedNestedDominationStrict_of_covariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPeriodicRepair.lean)
-/
@[path]
private lemma periodicWeightedNestedDominationStrict_of_covariant_eq
  {d n : Nat}
  {q beta : Real}
-- given
  (J : Sym2 (Site d) -> Real)
  (hJ : forall e, 0 < J e)
  (phase : Site d -> P)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hcov : PhaseCovariant J phase phaseJ)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  PeriodicWeightedNestedDominationStrict d n J phase phaseJ q beta := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPeriodicRepair.periodicWeightedNestedDominationStrict_of_covariant d n J hJ phase phaseJ hcov q beta hq hbeta


-- created on 2026-10-23
