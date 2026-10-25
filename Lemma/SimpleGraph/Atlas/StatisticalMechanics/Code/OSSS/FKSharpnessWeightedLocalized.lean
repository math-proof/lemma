import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedLocalized
open Finset Set StatMech StatMech.OSSS StatMech.OSSS.FKSharpnessWeightedLocalized


/--
[weighted_outer_inner_hcov](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedLocalized.lean)
-/
@[path]
private lemma weighted_outer_inner_hcov_eq
  {d n : Nat}
  {q beta D : Real}
-- given
  (hn : 1 <= n)
  (J : Sym2 (Site d) -> Real)
  (hJ : forall e, 0 < J e)
  (hq : 1 <= q)
  (hbeta : 0 < beta)
  (hD : 0 < D)
  (hsum : forall i : (boxGraph d n).edgeSet, (∑ k : ↑(Finset.Icc 1 n), localizedBoxReveal (activeBCProb (boxGraph d (2 * n)) (wiredBoxBoundaryGraph d (2 * n)) (betaParams (boxCoupling J (2 * n)) beta) q) (boxActiveEdgeLE d (n_le_two_mul n)) (boxActiveEdge d n) (boxActiveEndU d n) (boxActiveEndV d n) (k : Nat) i) <= (Fintype.card (↑(Finset.Icc 1 n)) : Real) * D) :
-- imply
  weightedLocalizedTheta d n J q beta * (1 - weightedLocalizedTheta d n J q beta) / D <= ∑ e, Lindeberg.cov (activeBCProb (boxGraph d (2 * n)) (wiredBoxBoundaryGraph d (2 * n)) (betaParams (boxCoupling J (2 * n)) beta) q) (innerCrossInd d n) (Lindeberg.coord e) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedLocalized.weighted_outer_inner_hcov d n hn J hJ q beta D hq hbeta hD hsum

/--
[weighted_outer_inner_hcov_geom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedLocalized.lean)
-/
@[path]
private lemma weighted_outer_inner_hcov_geom_eq
  {d n : Nat}
  {q beta : Real}
-- given
  (hn : 1 <= n)
  (J : Sym2 (Site d) -> Real)
  (hJ : forall e, 0 < J e)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  weightedLocalizedTheta d n J q beta * (1 - weightedLocalizedTheta d n J q beta) / weightedStrictDenom d n J q beta <= ∑ e, Lindeberg.cov (activeBCProb (boxGraph d (2 * n)) (wiredBoxBoundaryGraph d (2 * n)) (betaParams (boxCoupling J (2 * n)) beta) q) (innerCrossInd d n) (Lindeberg.coord e) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedLocalized.weighted_outer_inner_hcov_geom d n hn J hJ q beta hq hbeta

/--
[weightedLocalizedTheta_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedLocalized.lean)
-/
@[path]
private lemma weightedLocalizedTheta_nonneg_eq
  {d n : Nat}
  {q beta : Real}
-- given
  (J : Sym2 (Site d) -> Real)
  (hJ : forall e, 0 < J e)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  0 <= weightedLocalizedTheta d n J q beta := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedLocalized.weightedLocalizedTheta_nonneg d n J hJ q beta hq hbeta

/--
[weightedLocalizedTheta_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedLocalized.lean)
-/
@[path]
private lemma weightedLocalizedTheta_le_one_eq
  {d n : Nat}
  {q beta : Real}
-- given
  (J : Sym2 (Site d) -> Real)
  (hJ : forall e, 0 < J e)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  weightedLocalizedTheta d n J q beta <= 1 := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedLocalized.weightedLocalizedTheta_le_one d n J hJ q beta hq hbeta

/--
[weighted_outer_inner_hcov_phaseEnvelope](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedLocalized.lean)
-/
@[path]
private lemma weighted_outer_inner_hcov_phaseEnvelope_eq
  {d n : Nat}
  [Fintype P]
  [Nonempty P]
  {q beta : Real}
-- given
  (hn : 1 <= n)
  (J : Sym2 (Site d) -> Real)
  (hJ : forall e, 0 < J e)
  (phase : Site d -> P)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hsurj : Function.Surjective phase)
  (hcov : PhaseCovariant J phase phaseJ)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  weightedLocalizedTheta d n J q beta * (1 - weightedLocalizedTheta d n J q beta) / (8 * weightedPhaseEnvelopeSig d n phaseJ q beta / (n : Real)) <= ∑ e, Lindeberg.cov (activeBCProb (boxGraph d (2 * n)) (wiredBoxBoundaryGraph d (2 * n)) (betaParams (boxCoupling J (2 * n)) beta) q) (innerCrossInd d n) (Lindeberg.coord e) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedLocalized.weighted_outer_inner_hcov_phaseEnvelope d n hn J hJ phase phaseJ hsurj hcov q beta hq hbeta

/--
[weighted_outer_inner_differential_phaseEnvelope](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedLocalized.lean)
-/
@[path]
private lemma weighted_outer_inner_differential_phaseEnvelope_eq
  {d n : Nat}
  [Fintype P]
  [Nonempty P]
  {q beta : Real}
-- given
  (hd : 1 <= d)
  (hn : 1 <= n)
  (J : Sym2 (Site d) -> Real)
  (hJ : forall e, 0 < J e)
  (phase : Site d -> P)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hsurj : Function.Surjective phase)
  (hcovPhase : PhaseCovariant J phase phaseJ)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  exists cR : Real, 0 < cR ∧ cR * (weightedLocalizedTheta d n J q beta * (1 - weightedLocalizedTheta d n J q beta) / (8 * weightedPhaseEnvelopeSig d n phaseJ q beta / (n : Real))) <= deriv (fun b => activeBCMean (boxGraph d (2 * n)) (wiredBoxBoundaryGraph d (2 * n)) (betaParams (boxCoupling J (2 * n)) b) q (innerCrossInd d n)) beta := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedLocalized.weighted_outer_inner_differential_phaseEnvelope d n hd hn J hJ phase phaseJ hsurj hcovPhase q beta hq hbeta

/--
[weighted_outer_inner_differential_phaseEnvelope_uniform](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedLocalized.lean)
-/
@[path]
private lemma weighted_outer_inner_differential_phaseEnvelope_uniform_eq
  {d n : Nat}
  [Fintype P]
  [Nonempty P]
  {Jmin : Real}
  {q beta : Real}
-- given
  (hn : 1 <= n)
  (J : Sym2 (Site d) -> Real)
  (hJmin : 0 < Jmin)
  (hJlo : forall e, Jmin <= J e)
  (phase : Site d -> P)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hsurj : Function.Surjective phase)
  (hcovPhase : PhaseCovariant J phase phaseJ)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  Jmin * (weightedLocalizedTheta d n J q beta * (1 - weightedLocalizedTheta d n J q beta) / (8 * weightedPhaseEnvelopeSig d n phaseJ q beta / (n : Real))) <= deriv (fun b => activeBCMean (boxGraph d (2 * n)) (wiredBoxBoundaryGraph d (2 * n)) (betaParams (boxCoupling J (2 * n)) b) q (innerCrossInd d n)) beta := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedLocalized.weighted_outer_inner_differential_phaseEnvelope_uniform d n hn J Jmin hJmin hJlo phase phaseJ hsurj hcovPhase q beta hq hbeta


-- created on 2026-10-23
