import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedIntegration.Part2
open Finset Set MeasureTheory StatMech StatMech.OSSS StatMech.OSSS.FKSharpnessWeightedIntegration


/--
[weightedLocalizedTheta_one_sub_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedIntegration.lean)
-/
@[path]
private lemma weightedLocalizedTheta_one_sub_lower_eq
  {d n : Nat}
  {Jmin Jmax q beta beta0 : Real}
-- given
  (J : Sym2 (Site d) -> Real)
  (hJmin : 0 < Jmin)
  (hJlo : forall e, Jmin <= J e)
  (hJhi : forall e, J e <= Jmax)
  (hq : 1 <= q)
  (hbeta : 0 < beta)
  (hbeta0 : beta <= beta0) :
-- imply
  Real.exp (-(beta0 * Jmax)) ^ (2 * d) <= 1 - weightedLocalizedTheta d n J q beta := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedIntegration.weightedLocalizedTheta_one_sub_lower d n J Jmin Jmax q beta beta0 hJmin hJlo hJhi hq hbeta hbeta0

/--
[weighted_outer_inner_differential_absorbed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedIntegration.lean)
-/
@[path]
private lemma weighted_outer_inner_differential_absorbed_eq
  {d n : Nat}
  [Fintype P]
  [Nonempty P]
  {Jmin Jmax : Real}
  {q beta beta0 : Real}
-- given
  (hn : 1 <= n)
  (J : Sym2 (Site d) -> Real)
  (hJmin : 0 < Jmin)
  (hJlo : forall e, Jmin <= J e)
  (hJhi : forall e, J e <= Jmax)
  (phase : Site d -> P)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hsurj : Function.Surjective phase)
  (hcov : PhaseCovariant J phase phaseJ)
  (hq : 1 <= q)
  (hbeta : 0 < beta)
  (hbeta0 : beta <= beta0) :
-- imply
  Jmin * Real.exp (-(beta0 * Jmax)) ^ (2 * d) * (weightedLocalizedTheta d n J q beta / (8 * weightedPhaseEnvelopeSig d n phaseJ q beta / (n : Real))) <= deriv (fun b => activeBCMean (boxGraph d (2 * n)) (wiredBoxBoundaryGraph d (2 * n)) (betaParams (boxCoupling J (2 * n)) b) q (innerCrossInd d n)) beta := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedIntegration.weighted_outer_inner_differential_absorbed d n hn J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov q beta beta0 hq hbeta hbeta0

/--
[weighted_outer_inner_differential_integration](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedIntegration.lean)
-/
@[path]
private lemma weighted_outer_inner_differential_integration_eq
  {d n : Nat}
  [Fintype P]
  [Nonempty P]
  {Jmin Jmax : Real}
  {q beta beta0 : Real}
-- given
  (hn : 1 <= n)
  (J : Sym2 (Site d) -> Real)
  (hJmin : 0 < Jmin)
  (hJlo : forall e, Jmin <= J e)
  (hJhi : forall e, J e <= Jmax)
  (phase : Site d -> P)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hsurj : Function.Surjective phase)
  (hcov : PhaseCovariant J phase phaseJ)
  (hq : 1 <= q)
  (hbeta : 0 < beta)
  (hbeta0 : beta <= beta0) :
-- imply
  (Jmin * Real.exp (-(beta0 * Jmax)) ^ (2 * d) / 8) * (((n : Real) / weightedPhaseEnvelopeSig d n phaseJ q beta) * weightedLocalizedTheta d n J q beta) <= deriv (fun b => activeBCMean (boxGraph d (2 * n)) (wiredBoxBoundaryGraph d (2 * n)) (betaParams (boxCoupling J (2 * n)) b) q (innerCrossInd d n)) beta := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedIntegration.weighted_outer_inner_differential_integration d n hn J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov q beta beta0 hq hbeta hbeta0

/--
[weightedLocalizedTheta_eq_phaseProfile_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedIntegration.lean)
-/
@[path]
private lemma weightedLocalizedTheta_eq_phaseProfile_origin_eq
  {d n : Nat}
  {q beta : Real}
-- given
  (hn : 1 <= n)
  (J : Sym2 (Site d) -> Real)
  (phase : Site d -> P)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hcov : PhaseCovariant J phase phaseJ) :
-- imply
  weightedLocalizedTheta d n J q beta = weightedPhaseProfile d phaseJ (phase 0) q beta n := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedIntegration.weightedLocalizedTheta_eq_phaseProfile_origin d n hn J phase phaseJ hcov q beta

/--
[weightedPhaseProfile_differential_integration](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedIntegration.lean)
-/
@[path]
private lemma weightedPhaseProfile_differential_integration_eq
  {d n : Nat}
  [Fintype P]
  [Nonempty P]
  {Jmin Jmax : Real}
  {q beta beta0 : Real}
  {x : Site d}
-- given
  (hn : 1 <= n)
  (J : Sym2 (Site d) -> Real)
  (hJmin : 0 < Jmin)
  (hJlo : forall e, Jmin <= J e)
  (hJhi : forall e, J e <= Jmax)
  (phase : Site d -> P)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hsurj : Function.Surjective phase)
  (hcov : PhaseCovariant J phase phaseJ)
  (hq : 1 <= q)
  (hbeta : 0 < beta)
  (hbeta0 : beta <= beta0) :
-- imply
  (Jmin * Real.exp (-(beta0 * Jmax)) ^ (2 * d) / 8) * (((n : Real) / weightedPhaseEnvelopeSig d n phaseJ q beta) * weightedPhaseProfile d phaseJ (phase x) q beta n) <= deriv (fun b => weightedPhaseProfile d phaseJ (phase x) q b n) beta := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedIntegration.weightedPhaseProfile_differential_integration d n hn J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov q beta beta0 hq hbeta hbeta0 x

/--
[weightedPhaseProfile_differentiableAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedIntegration.lean)
-/
@[path]
private lemma weightedPhaseProfile_differentiableAt_eq
  {d n : Nat}
  {a : P}
  {q beta : Real}
-- given
  (hn : 1 <= n)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall a e, 0 < phaseJ a e)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  DifferentiableAt Real (fun b => weightedPhaseProfile d phaseJ a q b n) beta := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedIntegration.weightedPhaseProfile_differentiableAt d n hn phaseJ hJ a q beta hq hbeta

/--
[weightedPhaseEnvelopeSig_le_sumSig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedIntegration.lean)
-/
@[path]
private lemma weightedPhaseEnvelopeSig_le_sumSig_eq
  {d n : Nat}
  [Fintype P]
  [Nonempty P]
  {q beta : Real}
-- given
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall a e, 0 < phaseJ a e)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  weightedPhaseEnvelopeSig d n phaseJ q beta <= weightedPhaseSumSig d n phaseJ q beta := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedIntegration.weightedPhaseEnvelopeSig_le_sumSig d n phaseJ hJ q beta hq hbeta

/--
[weightedPhaseSum_differential_integration](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedIntegration.lean)
-/
@[path]
private lemma weightedPhaseSum_differential_integration_eq
  {d n : Nat}
  [Fintype P]
  [Nonempty P]
  {Jmin Jmax : Real}
  {q beta beta0 : Real}
-- given
  (hn : 1 <= n)
  (J : Sym2 (Site d) -> Real)
  (hJmin : 0 < Jmin)
  (hJlo : forall e, Jmin <= J e)
  (hJhi : forall e, J e <= Jmax)
  (phase : Site d -> P)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hsurj : Function.Surjective phase)
  (hcov : PhaseCovariant J phase phaseJ)
  (hq : 1 <= q)
  (hbeta : 0 < beta)
  (hbeta0 : beta <= beta0) :
-- imply
  (Jmin * Real.exp (-(beta0 * Jmax)) ^ (2 * d) / 8) * (((n : Real) / weightedPhaseSumSig d n phaseJ q beta) * weightedPhaseSum d phaseJ q beta n) <= deriv (fun b => weightedPhaseSum d phaseJ q b n) beta := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedIntegration.weightedPhaseSum_differential_integration d n hn J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov q beta beta0 hq hbeta hbeta0

/--
[weightedPhasePhysical_le_localized_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedIntegration.lean)
-/
@[path]
private lemma weightedPhasePhysical_le_localized_half_eq
  {d n : Nat}
  {a : P}
  {q beta : Real}
-- given
  (hn : 2 <= n)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall a e, 0 < phaseJ a e)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  ((weightedPhaseFiniteMeasure d n phaseJ a (hJ a) q beta (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure _) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n) <= weightedPhaseProfile d phaseJ a q beta (n / 2) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedIntegration.weightedPhasePhysical_le_localized_half d n hn phaseJ hJ a q beta hq hbeta


-- created on 2026-10-23
