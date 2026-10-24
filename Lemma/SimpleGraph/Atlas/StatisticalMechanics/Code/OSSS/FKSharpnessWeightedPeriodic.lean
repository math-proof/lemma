import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedPeriodic
open Finset Set Filter Topology StatMech StatMech.OSSS StatMech.OSSS.FKSharpnessWeightedPeriodic


/--
[transBoxCoupling_map_eq_phaseBoxCoupling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPeriodic.lean)
-/
@[path]
private lemma transBoxCoupling_map_eq_phaseBoxCoupling_eq
  {d : Nat}
  {R : Nat}
  {x : Site d}
  {e : Sym2 (boxVerts d R)}
-- given
  (J : Sym2 (Site d) -> Real)
  (phase : Site d -> P)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hcov : PhaseCovariant J phase phaseJ) :
-- imply
  transBoxCoupling J R x (Sym2.map (fvs_transEquiv d R x) e) = phaseBoxCoupling phaseJ (phase x) R e := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPeriodic.transBoxCoupling_map_eq_phaseBoxCoupling J phase phaseJ hcov R x e

/--
[PhaseCovariant.eq_of_same_phase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPeriodic.lean)
-/
@[path]
private lemma eq_of_same_phase_eq
  {d : Nat}
  {J : Sym2 (Site d) -> Real}
  {phase : Site d -> P}
  {phaseJ : P -> Sym2 (Site d) -> Real}
  {x y : Site d}
  {e : Sym2 (Site d)}
-- given
  (hcov : PhaseCovariant J phase phaseJ)
  (hxy : phase x = phase y) :
-- imply
  J (translateAmbientEdge x e) = J (translateAmbientEdge y e) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPeriodic.PhaseCovariant.eq_of_same_phase hcov hxy e

/--
[PhaseCovariant.phaseCoupling_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPeriodic.lean)
-/
@[path]
private lemma phaseCoupling_pos_eq
  {d : Nat}
  {J : Sym2 (Site d) -> Real}
  {phase : Site d -> P}
  {phaseJ : P -> Sym2 (Site d) -> Real}
-- given
  (hcov : PhaseCovariant J phase phaseJ)
  (hsurj : Function.Surjective phase)
  (hJ : forall e, 0 < J e) :
-- imply
  forall a e, 0 < phaseJ a e := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPeriodic.PhaseCovariant.phaseCoupling_pos hcov hsurj hJ

/--
[betaParams_transBox_map_eq_phaseBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPeriodic.lean)
-/
@[path]
private lemma betaParams_transBox_map_eq_phaseBox_eq
  {d : Nat}
  {R : Nat}
  {x : Site d}
  {beta : Real}
  {e : Sym2 (boxVerts d R)}
-- given
  (J : Sym2 (Site d) -> Real)
  (phase : Site d -> P)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hcov : PhaseCovariant J phase phaseJ) :
-- imply
  FK.betaParams (transBoxCoupling J R x) beta (Sym2.map (fvs_transEquiv d R x) e) = FK.betaParams (phaseBoxCoupling phaseJ (phase x) R) beta e := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPeriodic.betaParams_transBox_map_eq_phaseBox J phase phaseJ hcov R x beta e

/--
[weightedPhaseWiredTheta_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPeriodic.lean)
-/
@[path]
private lemma weightedPhaseWiredTheta_nonneg_eq
  {d : Nat}
  {a : P}
  {q beta : Real}
  {k : Nat}
-- given
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall a e, 0 < phaseJ a e)
  (hq : 0 < q)
  (hbeta : 0 < beta) :
-- imply
  0 <= weightedPhaseWiredTheta d phaseJ a q beta k := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPeriodic.weightedPhaseWiredTheta_nonneg d phaseJ hJ a q beta hq hbeta k

/--
[le_phaseEnvelope](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPeriodic.lean)
-/
@[path]
private lemma le_phaseEnvelope_eq
  [Fintype P]
  [Nonempty P]
  {a : P}
  {n : Nat}
-- given
  (theta : P -> Nat -> Real) :
-- imply
  theta a n <= phaseEnvelope theta n := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPeriodic.le_phaseEnvelope theta a n

/--
[phaseEnvelope_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPeriodic.lean)
-/
@[path]
private lemma phaseEnvelope_nonneg_eq
  [Fintype P]
  [Nonempty P]
  {n : Nat}
-- given
  (theta : P -> Nat -> Real)
  (htheta : forall a n, 0 <= theta a n) :
-- imply
  0 <= phaseEnvelope theta n := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPeriodic.phaseEnvelope_nonneg theta htheta n

/--
[weightedWiredActiveDenom_le_phaseDenom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPeriodic.lean)
-/
@[path]
private lemma weightedWiredActiveDenom_le_phaseDenom_eq
  {d n : Nat}
  [Fintype P]
  [Nonempty P]
  {q beta : Real}
-- given
  (J : Sym2 (boxVerts d n) -> Real)
  (phase : Site d -> P)
  (theta : P -> Nat -> Real)
  (hoff : WeightedPhaseOffCentre d n J phase theta q beta) :
-- imply
  weightedWiredActiveDenom d n J q beta <= weightedPhaseDenom theta n := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPeriodic.weightedWiredActiveDenom_le_phaseDenom d n J phase theta q beta hoff

/--
[weightedPhaseDenom_pos_of_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPeriodic.lean)
-/
@[path]
private lemma weightedPhaseDenom_pos_of_pos_eq
  [Fintype P]
  [Nonempty P]
  {n k : Nat}
  {a : P}
-- given
  (theta : P -> Nat -> Real)
  (htheta : forall a k, 0 <= theta a k)
  (hk : k ∈ Finset.range n)
  (hpos : 0 < theta a k) :
-- imply
  0 < weightedPhaseDenom theta n := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPeriodic.weightedPhaseDenom_pos_of_pos theta htheta n k hk a hpos

/--
[weighted_wired_box_phase_differential_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPeriodic.lean)
-/
@[path]
private lemma weighted_wired_box_phase_differential_inequality_eq
  {d n : Nat}
  [Fintype P]
  [Nonempty P]
  {q beta beta0 : Real}
-- given
  (hd : 1 <= d)
  (hn : 1 <= n)
  (J : Sym2 (boxVerts d n) -> Real)
  (hJ : forall e, 0 < J e)
  (phase : Site d -> P)
  (theta : P -> Nat -> Real)
  (hq : 1 <= q)
  (hbeta : 0 < beta)
  (hbeta0 : beta <= beta0)
  (hoff : WeightedPhaseOffCentre d n J phase theta q beta) :
-- imply
  exists c : Real, 0 < c ∧ c * (weightedWiredActiveTheta d n J q beta / weightedPhaseDenom theta n) <= deriv (fun b => FK.activeBCProbOf (boxGraph d n) (wiredBoxBoundaryGraph d n) (FK.betaParams J b) q (crossEvent (boxActiveEdge d n) 0 (vertexBoundary d n))) beta := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPeriodic.weighted_wired_box_phase_differential_inequality d n hd hn J hJ phase theta q beta beta0 hq hbeta hbeta0 hoff

/--
[weighted_wired_box_differential_uniform_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPeriodic.lean)
-/
@[path]
private lemma weighted_wired_box_differential_uniform_bounds_eq
  {d n : Nat}
  {Jmin Jmax q beta beta0 : Real}
-- given
  (hd : 1 <= d)
  (hn : 1 <= n)
  (J : Sym2 (boxVerts d n) -> Real)
  (hJmin : 0 < Jmin)
  (hJlo : forall e, Jmin <= J e)
  (hJhi : forall e, J e <= Jmax)
  (hq : 1 <= q)
  (hbeta : 0 < beta)
  (hbeta0 : beta <= beta0) :
-- imply
  Jmin * Real.exp (-(beta0 * Jmax)) ^ (2 * d) * (weightedWiredActiveTheta d n J q beta / weightedWiredActiveDenom d n J q beta) <= deriv (fun b => FK.activeBCProbOf (boxGraph d n) (wiredBoxBoundaryGraph d n) (FK.betaParams J b) q (crossEvent (boxActiveEdge d n) 0 (vertexBoundary d n))) beta := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPeriodic.weighted_wired_box_differential_uniform_bounds d n hd hn J Jmin Jmax q beta beta0 hJmin hJlo hJhi hq hbeta hbeta0

/--
[weighted_periodic_box_differential_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPeriodic.lean)
-/
@[path]
private lemma weighted_periodic_box_differential_inequality_eq
  {d n : Nat}
  [Fintype P]
  [Nonempty P]
  {q beta beta0 : Real}
-- given
  (hd : 1 <= d)
  (hn : 1 <= n)
  (J : Sym2 (Site d) -> Real)
  (hJ : forall e, 0 < J e)
  (phase : Site d -> P)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hq : 1 <= q)
  (hbeta : 0 < beta)
  (hbeta0 : beta <= beta0)
  (hnested : PeriodicWeightedNestedDomination d n J phase phaseJ q beta) :
-- imply
  exists c : Real, 0 < c ∧ c * (weightedWiredActiveTheta d n (boxCoupling J n) q beta / weightedPhaseDenom (fun a => weightedPhaseWiredTheta d phaseJ a q beta) n) <= deriv (fun b => FK.activeBCProbOf (boxGraph d n) (wiredBoxBoundaryGraph d n) (FK.betaParams (boxCoupling J n) b) q (crossEvent (boxActiveEdge d n) 0 (vertexBoundary d n))) beta := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPeriodic.weighted_periodic_box_differential_inequality d n hd hn J hJ phase phaseJ q beta beta0 hq hbeta hbeta0 hnested

/--
[weighted_periodic_box_differential_uniform_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPeriodic.lean)
-/
@[path]
private lemma weighted_periodic_box_differential_uniform_bounds_eq
  {d n : Nat}
  [Fintype P]
  [Nonempty P]
  {Jmin Jmax : Real}
  {q beta beta0 : Real}
-- given
  (hd : 1 <= d)
  (hn : 1 <= n)
  (J : Sym2 (Site d) -> Real)
  (hJmin : 0 < Jmin)
  (hJlo : forall e, Jmin <= J e)
  (hJhi : forall e, J e <= Jmax)
  (phase : Site d -> P)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hq : 1 <= q)
  (hbeta : 0 < beta)
  (hbeta0 : beta <= beta0)
  (hnested : PeriodicWeightedNestedDomination d n J phase phaseJ q beta) :
-- imply
  Jmin * Real.exp (-(beta0 * Jmax)) ^ (2 * d) * (weightedWiredActiveTheta d n (boxCoupling J n) q beta / weightedPhaseDenom (fun a => weightedPhaseWiredTheta d phaseJ a q beta) n) <= deriv (fun b => FK.activeBCProbOf (boxGraph d n) (wiredBoxBoundaryGraph d n) (FK.betaParams (boxCoupling J n) b) q (crossEvent (boxActiveEdge d n) 0 (vertexBoundary d n))) beta := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPeriodic.weighted_periodic_box_differential_uniform_bounds d n hd hn J Jmin Jmax hJmin hJlo hJhi phase phaseJ q beta beta0 hq hbeta hbeta0 hnested

/--
[tendsto_finset_sup'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPeriodic.lean)
-/
@[path]
private lemma tendsto_finset_sup'_eq
  [DecidableEq P]
  {l : Filter X}
  {s : Finset P}
-- given
  (hs : s.Nonempty)
  (f : P -> X -> Real)
  (a : P -> Real)
  (hf : forall p, p ∈ s -> Tendsto (f p) l (nhds (a p))) :
-- imply
  Tendsto (fun x => s.sup' hs (fun p => f p x)) l (nhds (s.sup' hs a)) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPeriodic.tendsto_finset_sup' s hs f a hf

/--
[phaseEnvelope_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPeriodic.lean)
-/
@[path]
private lemma phaseEnvelope_tendsto_eq
  [Fintype P]
  [Nonempty P]
-- given
  (theta : P -> Nat -> Real)
  (thetaInf : P -> Real)
  (hlim : forall a, Tendsto (theta a) atTop (nhds (thetaInf a))) :
-- imply
  Tendsto (phaseEnvelope theta) atTop (nhds (Finset.univ.sup' Finset.univ_nonempty thetaInf)) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPeriodic.phaseEnvelope_tendsto theta thetaInf hlim

/--
[phaseSup_pos_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPeriodic.lean)
-/
@[path]
private lemma phaseSup_pos_iff_eq
  [Fintype P]
  [Nonempty P]
-- given
  (thetaInf : P -> Real) :
-- imply
  0 < Finset.univ.sup' Finset.univ_nonempty thetaInf ↔ exists a, 0 < thetaInf a := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPeriodic.phaseSup_pos_iff thetaInf

/--
[phaseSup_transition_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPeriodic.lean)
-/
@[path]
private lemma phaseSup_transition_iff_eq
  [Fintype P]
  [Nonempty P]
  {betaC beta : Real}
-- given
  (thetaInf : P -> Real -> Real)
  (hphase : forall a, 0 < thetaInf a beta ↔ betaC < beta) :
-- imply
  0 < Finset.univ.sup' Finset.univ_nonempty (fun a => thetaInf a beta) ↔ betaC < beta := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPeriodic.phaseSup_transition_iff thetaInf betaC beta hphase

/--
[phaseSup_zeroSet_eq_Iic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPeriodic.lean)
-/
@[path]
private lemma phaseSup_zeroSet_eq_Iic_eq
  [Fintype P]
  [Nonempty P]
  {betaC : Real}
-- given
  (thetaInf : P -> Real -> Real)
  (hnonneg : forall a beta, 0 <= thetaInf a beta)
  (hphase : forall a beta, 0 < thetaInf a beta ↔ betaC < beta) :
-- imply
  {beta | Finset.univ.sup' Finset.univ_nonempty (fun a => thetaInf a beta) = 0} = Set.Iic betaC := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPeriodic.phaseSup_zeroSet_eq_Iic thetaInf betaC hnonneg hphase

/--
[phaseSup_critical_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPeriodic.lean)
-/
@[path]
private lemma phaseSup_critical_eq_eq
  [Fintype P]
  [Nonempty P]
  {betaC : Real}
-- given
  (thetaInf : P -> Real -> Real)
  (hnonneg : forall a beta, 0 <= thetaInf a beta)
  (hphase : forall a beta, 0 < thetaInf a beta ↔ betaC < beta) :
-- imply
  sSup {beta | Finset.univ.sup' Finset.univ_nonempty (fun a => thetaInf a beta) = 0} = betaC := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPeriodic.phaseSup_critical_eq thetaInf betaC hnonneg hphase


-- created on 2026-10-23
