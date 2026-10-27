import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheAnalyticContinuation.Part2
open Filter Topology StatMech StatMech.FrontierD


/--
[analyticOnNhd_sixVertexHalfFilledPerronNormalized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheAnalyticContinuation.lean)
-/
@[path]
private lemma analyticOnNhd_sixVertexHalfFilledPerronNormalized_eq
  {k : Nat} :
-- imply
  AnalyticOnNhd Real (sixVertexHalfFilledPerronNormalized k) (Set.Ioi 2) := by
-- proof
  apply StatMech.FrontierD.analyticOnNhd_sixVertexHalfFilledPerronNormalized k

/--
[sixVertexHalfFilledCandidateNormalized_eq_kernelAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheAnalyticContinuation.lean)
-/
@[path]
private lemma sixVertexHalfFilledCandidateNormalized_eq_kernelAt_eq
  {k : Nat}
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexHalfFilledBetheCandidateNormalized k c = sixVertexHalfFilledCandidateKernelAt k c := by
-- proof
  apply StatMech.FrontierD.sixVertexHalfFilledCandidateNormalized_eq_kernelAt k hc

/--
[analyticOnNhd_sixVertexHalfFilledBetheCandidateNormalized_of_roots](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheAnalyticContinuation.lean)
-/
@[path]
private lemma analyticOnNhd_sixVertexHalfFilledBetheCandidateNormalized_of_roots_eq
  {k : Nat}
-- given
  (hroots : ∀ j : Fin (k + 1), AnalyticOnNhd Real (fun c => sixVertexHalfFilledBetheRootAt k (Fin.natAdd (k + 1) j) c) (Set.Ioi 2)) :
-- imply
  AnalyticOnNhd Real (sixVertexHalfFilledBetheCandidateNormalized k) (Set.Ioi 2) := by
-- proof
  apply StatMech.FrontierD.analyticOnNhd_sixVertexHalfFilledBetheCandidateNormalized_of_roots k hroots

/--
[eventually_sixVertexHalfFilledCandidateNormalized_eq_perronNormalized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheAnalyticContinuation.lean)
-/
@[path]
private lemma eventually_sixVertexHalfFilledCandidateNormalized_eq_perronNormalized_eq
  {k : Nat} :
-- imply
  sixVertexHalfFilledBetheCandidateNormalized k =ᶠ[atTop] sixVertexHalfFilledPerronNormalized k := by
-- proof
  apply StatMech.FrontierD.eventually_sixVertexHalfFilledCandidateNormalized_eq_perronNormalized k

/--
[sixVertexHalfFilledCandidateNormalized_eq_perronNormalized_of_analytic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheAnalyticContinuation.lean)
-/
@[path]
private lemma sixVertexHalfFilledCandidateNormalized_eq_perronNormalized_of_analytic_eq
  {k : Nat}
-- given
  (hcandidate : AnalyticOnNhd Real (sixVertexHalfFilledBetheCandidateNormalized k) (Set.Ioi 2))
  (hperron : AnalyticOnNhd Real (sixVertexHalfFilledPerronNormalized k) (Set.Ioi 2)) :
-- imply
  Set.EqOn (sixVertexHalfFilledBetheCandidateNormalized k) (sixVertexHalfFilledPerronNormalized k) (Set.Ioi 2) := by
-- proof
  apply StatMech.FrontierD.sixVertexHalfFilledCandidateNormalized_eq_perronNormalized_of_analytic k hcandidate hperron

/--
[sixVertexHalfFilledCandidate_eq_perron_of_analytic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheAnalyticContinuation.lean)
-/
@[path]
private lemma sixVertexHalfFilledCandidate_eq_perron_of_analytic_eq
  {c : Real}
  {k : Nat}
-- given
  (hc : 2 < c)
  (hcandidate : AnalyticOnNhd Real (sixVertexHalfFilledBetheCandidateNormalized k) (Set.Ioi 2))
  (hperron : AnalyticOnNhd Real (sixVertexHalfFilledPerronNormalized k) (Set.Ioi 2)) :
-- imply
  sixVertexSymmetricBetheEigenvalueValue c (sixVertexPositiveHalfBetheRoots hc k) = sixVertexSectorTopEigenvalue (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) (by unfold sixVertexFourWidth omega) c := by
-- proof
  apply StatMech.FrontierD.sixVertexHalfFilledCandidate_eq_perron_of_analytic hc k hcandidate hperron

/--
[sixVertexHasSymmetricBetheIdentification_of_analyticBranches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheAnalyticContinuation.lean)
-/
@[path]
private lemma sixVertexHasSymmetricBetheIdentification_of_analyticBranches_eq
  {c : Real}
-- given
  (hc : 2 < c)
  (hcandidate : ∀ k, AnalyticOnNhd Real (sixVertexHalfFilledBetheCandidateNormalized k) (Set.Ioi 2))
  (hperron : ∀ k, AnalyticOnNhd Real (sixVertexHalfFilledPerronNormalized k) (Set.Ioi 2)) :
-- imply
  SixVertexHasSymmetricBetheIdentification c (sixVertexPositiveHalfBetheRootFamily hc) := by
-- proof
  apply StatMech.FrontierD.sixVertexHasSymmetricBetheIdentification_of_analyticBranches hc hcandidate hperron

/--
[sixVertexHasSymmetricBetheIdentification_of_analyticRoots](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheAnalyticContinuation.lean)
-/
@[path]
private lemma sixVertexHasSymmetricBetheIdentification_of_analyticRoots_eq
  {c : Real}
-- given
  (hc : 2 < c)
  (hroots : ∀ k (j : Fin (k + 1)), AnalyticOnNhd Real (fun t => sixVertexHalfFilledBetheRootAt k (Fin.natAdd (k + 1) j) t) (Set.Ioi 2)) :
-- imply
  SixVertexHasSymmetricBetheIdentification c (sixVertexPositiveHalfBetheRootFamily hc) := by
-- proof
  apply StatMech.FrontierD.sixVertexHasSymmetricBetheIdentification_of_analyticRoots hc hroots


-- created on 2026-10-23
