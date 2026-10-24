import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedDensityCandidate
open StatMech StatMech.FrontierD


/--
[eventually_sixVertexCanonicalFixedEvenDensityBetheEigenvalueValue_eq_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedDensityCandidate.lean)
-/
@[path]
private lemma eventually_sixVertexCanonicalFixedEvenDensityBetheEigenvalueValue_eq_top_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  ∀ᶠ k : Nat in atTop, sixVertexCanonicalFixedEvenDensityBetheEigenvalueValue hc s k = sixVertexSectorTopEigenvalue (sixVertexFourWidth (2 * s) k) ((s + k + 1) + (s + k + 1)) (by unfold sixVertexFourWidth omega) c := by
-- proof
  apply StatMech.FrontierD.eventually_sixVertexCanonicalFixedEvenDensityBetheEigenvalueValue_eq_top hc s

/--
[eventually_sixVertexCanonicalFixedOddDensityBetheEigenvalueValue_eq_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedDensityCandidate.lean)
-/
@[path]
private lemma eventually_sixVertexCanonicalFixedOddDensityBetheEigenvalueValue_eq_top_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  ∀ᶠ k : Nat in atTop, sixVertexCanonicalFixedOddDensityBetheEigenvalueValue hc s k = sixVertexSectorTopEigenvalue (sixVertexFourWidth (2 * s + 1) k) (((s + k + 1) + 1) + (s + k + 1)) (by unfold sixVertexFourWidth omega) c := by
-- proof
  apply StatMech.FrontierD.eventually_sixVertexCanonicalFixedOddDensityBetheEigenvalueValue_eq_top hc s

/--
[eventually_sixVertexCanonicalFixedEvenDensityBetheEigenvalueValue_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedDensityCandidate.lean)
-/
@[path]
private lemma eventually_sixVertexCanonicalFixedEvenDensityBetheEigenvalueValue_eq_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexCanonicalFixedEvenDensityBetheEigenvalueValue hc s =ᶠ[atTop] sixVertexCanonicalFixedEvenChargeBetheEigenvalueValue hc s := by
-- proof
  apply StatMech.FrontierD.eventually_sixVertexCanonicalFixedEvenDensityBetheEigenvalueValue_eq hc s

/--
[eventually_sixVertexCanonicalFixedOddDensityBetheEigenvalueValue_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedDensityCandidate.lean)
-/
@[path]
private lemma eventually_sixVertexCanonicalFixedOddDensityBetheEigenvalueValue_eq_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexCanonicalFixedOddDensityBetheEigenvalueValue hc s =ᶠ[atTop] sixVertexCanonicalFixedOddChargeBetheEigenvalueValue hc s := by
-- proof
  apply StatMech.FrontierD.eventually_sixVertexCanonicalFixedOddDensityBetheEigenvalueValue_eq hc s

/--
[sixVertexCanonicalFixedEvenDensityCandidateLogRatio_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedDensityCandidate.lean)
-/
@[path]
private lemma sixVertexCanonicalFixedEvenDensityCandidateLogRatio_eq_eq
  {c : Real}
  {s k : Nat}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexCanonicalFixedEvenDensityCandidateLogRatio hc s k = 2 * ((∑ j, sixVertexBetheLogObservable c (sixVertexCanonicalFixedEvenDensityPositiveRoots hc s k j)) - ∑ j, sixVertexBetheLogObservable c (sixVertexCanonicalDensityPerronPositiveHalfRoots hc (2 * s + k) j)) := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalFixedEvenDensityCandidateLogRatio_eq hc s k

/--
[sixVertexCanonicalFixedOddDensityPerronBetheRoots_central_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedDensityCandidate.lean)
-/
@[path]
private lemma sixVertexCanonicalFixedOddDensityPerronBetheRoots_central_eq_zero_eq
  {c : Real}
  {s k : Nat}
-- given
  (hc : 2 < c)
  (hfixed : SixVertexCanonicalFixedOddDensityWitness hc s k (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k)) :
-- imply
  sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k (sixVertexOddCentralIndex (s + k + 1)) = 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalFixedOddDensityPerronBetheRoots_central_eq_zero hc s k hfixed

/--
[sum_erase_central_sixVertexBetheLogObservable_oddSymmetric](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedDensityCandidate.lean)
-/
@[path]
private lemma sum_erase_central_sixVertexBetheLogObservable_oddSymmetric_eq
  {c : Real}
  {m : Nat}
  {p : Fin ((m + 1) + m) -> Real}
-- given
  (hp : SixVertexRootSymmetric p) :
-- imply
  (∑ j ∈ Finset.univ.erase (sixVertexOddCentralIndex m), sixVertexBetheLogObservable c (p j)) = 2 * ∑ j : Fin m, sixVertexBetheLogObservable c (sixVertexOddPositiveHalfProjection m p j) := by
-- proof
  apply StatMech.FrontierD.sum_erase_central_sixVertexBetheLogObservable_oddSymmetric c m hp

/--
[sixVertexCanonicalFixedOddDensityCandidateLogRatio_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedDensityCandidate.lean)
-/
@[path]
private lemma sixVertexCanonicalFixedOddDensityCandidateLogRatio_eq_eq
  {c : Real}
  {s k : Nat}
-- given
  (hc : 2 < c)
  (hfixed : SixVertexCanonicalFixedOddDensityWitness hc s k (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k)) :
-- imply
  sixVertexCanonicalFixedOddDensityCandidateLogRatio hc s k = Real.log (sixVertexZeroPhaseBethePrefactor c (sixVertexFourWidth (2 * s + 1) k) (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k) (sixVertexOddCentralIndex (s + k + 1))) - Real.log 2 + 2 * ((∑ j, sixVertexBetheLogObservable c (sixVertexCanonicalFixedOddDensityPositiveRoots hc s k j)) - ∑ j, sixVertexBetheLogObservable c (sixVertexCanonicalDensityPerronPositiveHalfRoots hc (2 * s + 1 + k) j)) := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalFixedOddDensityCandidateLogRatio_eq hc s k hfixed


-- created on 2026-10-23
