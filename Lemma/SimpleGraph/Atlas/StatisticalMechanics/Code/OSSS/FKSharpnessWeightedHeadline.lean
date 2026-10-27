import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedHeadline
open Finset Set MeasureTheory StatMech StatMech.OSSS StatMech.OSSS.FKSharpnessWeightedHeadline


/--
[weightedPhaseFiniteBoundaryMass_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedHeadline.lean)
-/
@[path]
private lemma weightedPhaseFiniteBoundaryMass_lt_one_eq
  {d n : Nat}
  {a : P}
  {q beta : Real}
-- given
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall e, 0 < phaseJ a e)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  ((weightedPhaseFiniteMeasure d n phaseJ a hJ q beta (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure _) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n) < 1 := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedHeadline.weightedPhaseFiniteBoundaryMass_lt_one d n phaseJ a hJ q beta hq hbeta

/--
[weightedPeriodicSharpness_all_radii_of_two_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedHeadline.lean)
-/
@[path]
private lemma weightedPeriodicSharpness_all_radii_of_two_le_eq
  {d : Nat}
  [Fintype P]
  [Nonempty P]
  {Jmin Jmax : Real}
  {q : Real}
-- given
  (hd : 2 <= d)
  (J : Sym2 (Site d) -> Real)
  (hJmin : 0 < Jmin)
  (hJlo : forall e, Jmin <= J e)
  (hJhi : forall e, J e <= Jmax)
  (phase : Site d -> P)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hsurj : Function.Surjective phase)
  (hcov : PhaseCovariant J phase phaseJ)
  (hq : 1 <= q) :
-- imply
  exists beta0 betaC kappa : Real, 0 < betaC /\ betaC < beta0 /\ 0 < kappa /\ (forall a : P, sSup (BetaCMatch.bcm_subcriticalSet (weightedPhaseThetaProfile d phaseJ (hcov.phaseCoupling_pos hsurj (fun e => hJmin.trans_le (hJlo e))) q (zero_lt_one.trans_le hq) a)) = betaC) /\ (forall a beta, betaC <= beta -> beta <= beta0 -> (kappa / Fintype.card P) * weightedPhaseSharpConstant d Jmin Jmax beta0 * (beta - betaC) <= weightedPhaseThetaProfile d phaseJ (hcov.phaseCoupling_pos hsurj (fun e => hJmin.trans_le (hJlo e))) q (zero_lt_one.trans_le hq) a beta) /\ forall gamma, (hgamma : 0 < gamma) -> gamma < betaC -> exists c : Real, 0 < c /\ forall a : P, forall n : Nat, ((weightedPhaseFiniteMeasure d n phaseJ a (hcov.phaseCoupling_pos hsurj (fun e => hJmin.trans_le (hJlo e)) a) q gamma (zero_lt_one.trans_le hq) hgamma : ProbabilityMeasure _) : Measure _).real (boxBdryConnEvent d n) <= Real.exp (-(c * (n : Real))) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedHeadline.weightedPeriodicSharpness_all_radii_of_two_le d hd J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov q hq


-- created on 2026-10-23
