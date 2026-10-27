import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalCandidateDecomposition
open StatMech StatMech.FrontierD


/--
[sixVertexCanonicalEvenAlignedHalfRoots_positive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalCandidateDecomposition.lean)
-/
@[path]
private lemma sixVertexCanonicalEvenAlignedHalfRoots_positive_eq
  {c : Real}
  {s k : Nat}
  {j : Fin (s + k + 1)}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexCanonicalEvenAlignedHalfRoots hc s k (Fin.natAdd (s + k + 1) j) = sixVertexCanonicalEvenCommonHalfRoot hc s k j := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalEvenAlignedHalfRoots_positive hc s k j

/--
[sixVertexCanonicalOddAlignedHalfRoots_positive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalCandidateDecomposition.lean)
-/
@[path]
private lemma sixVertexCanonicalOddAlignedHalfRoots_positive_eq
  {c : Real}
  {s k : Nat}
  {j : Fin (s + k + 1)}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexCanonicalOddAlignedHalfRoots hc s k (sixVertexOddPositiveIndex (s + k + 1) j) = sixVertexCanonicalOddMidpointHalfRoot hc s k j := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalOddAlignedHalfRoots_positive hc s k j

/--
[sum_sixVertexCanonicalEvenHalfRoots_eq_common_add_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalCandidateDecomposition.lean)
-/
@[path]
private lemma sum_sixVertexCanonicalEvenHalfRoots_eq_common_add_boundary_eq
  {c : Real}
  {s k : Nat}
-- given
  (f : Real -> Real)
  (hc : 2 < c) :
-- imply
  (∑ j, f (sixVertexCanonicalDensityPerronPositiveHalfRoots hc (2 * s + k) j)) = (∑ j, f (sixVertexCanonicalEvenCommonHalfRoot hc s k j)) + ∑ i, f (sixVertexCanonicalEvenBoundaryHalfRoot hc s k i) := by
-- proof
  apply StatMech.FrontierD.sum_sixVertexCanonicalEvenHalfRoots_eq_common_add_boundary f hc s k

/--
[sum_sixVertexCanonicalOddHalfRoots_eq_left_add_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalCandidateDecomposition.lean)
-/
@[path]
private lemma sum_sixVertexCanonicalOddHalfRoots_eq_left_add_boundary_eq
  {c : Real}
  {s k : Nat}
-- given
  (f : Real -> Real)
  (hc : 2 < c) :
-- imply
  (∑ j, f (sixVertexCanonicalDensityPerronPositiveHalfRoots hc (2 * s + 1 + k) j)) = (∑ j, f (sixVertexCanonicalOddLeftHalfRoot hc s k j)) + ∑ i, f (sixVertexCanonicalOddBoundaryHalfRoot hc s k i) := by
-- proof
  apply StatMech.FrontierD.sum_sixVertexCanonicalOddHalfRoots_eq_left_add_boundary f hc s k

/--
[abs_sixVertexCanonicalEvenBoundaryHalfRoot_sub_pi_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalCandidateDecomposition.lean)
-/
@[path]
private lemma abs_sixVertexCanonicalEvenBoundaryHalfRoot_sub_pi_le_eq
  {c : Real}
  {s k : Nat}
  {lower : Real}
  {i : Fin s}
-- given
  (hc : 2 < c)
  (hlower : 0 < lower)
  (hdensity : forall x, lower <= sixVertexFiniteRootDensity c (sixVertexFourWidth 0 (2 * s + k)) ((2 * s + k + 1) + (2 * s + k + 1)) (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + k)) x) :
-- imply
  |sixVertexCanonicalEvenBoundaryHalfRoot hc s k i - Real.pi| <= (s : Real) / ((sixVertexFourWidth 0 (2 * s + k) : Real) * lower) := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexCanonicalEvenBoundaryHalfRoot_sub_pi_le hc s k hlower hdensity i

/--
[abs_sixVertexCanonicalOddBoundaryHalfRoot_sub_pi_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalCandidateDecomposition.lean)
-/
@[path]
private lemma abs_sixVertexCanonicalOddBoundaryHalfRoot_sub_pi_le_eq
  {c : Real}
  {s k : Nat}
  {lower : Real}
  {i : Fin (s + 1)}
-- given
  (hc : 2 < c)
  (hlower : 0 < lower)
  (hdensity : forall x, lower <= sixVertexFiniteRootDensity c (sixVertexFourWidth 0 (2 * s + 1 + k)) ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)) (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)) x) :
-- imply
  |sixVertexCanonicalOddBoundaryHalfRoot hc s k i - Real.pi| <= (s + 1 : Real) / ((sixVertexFourWidth 0 (2 * s + 1 + k) : Real) * lower) := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexCanonicalOddBoundaryHalfRoot_sub_pi_le hc s k hlower hdensity i

/--
[sixVertexCanonicalFixedEvenDensityCandidateLogRatio_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalCandidateDecomposition.lean)
-/
@[path]
private lemma sixVertexCanonicalFixedEvenDensityCandidateLogRatio_decomposition_eq
  {c : Real}
  {s k : Nat}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexCanonicalFixedEvenDensityCandidateLogRatio hc s k = 2 * ( (∑ j, (sixVertexBetheLogObservable c (sixVertexCanonicalFixedEvenDensityPositiveRoots hc s k j) - sixVertexBetheLogObservable c (sixVertexCanonicalEvenCommonHalfRoot hc s k j))) - ∑ i, sixVertexBetheLogObservable c (sixVertexCanonicalEvenBoundaryHalfRoot hc s k i)) := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalFixedEvenDensityCandidateLogRatio_decomposition hc s k

/--
[sixVertexCanonicalFixedOddDensityCandidateLogRatio_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalCandidateDecomposition.lean)
-/
@[path]
private lemma sixVertexCanonicalFixedOddDensityCandidateLogRatio_decomposition_eq
  {c : Real}
  {s k : Nat}
-- given
  (hc : 2 < c)
  (hfixed : SixVertexCanonicalFixedOddDensityWitness hc s k (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k)) :
-- imply
  sixVertexCanonicalFixedOddDensityCandidateLogRatio hc s k = Real.log (sixVertexZeroPhaseBethePrefactor c (sixVertexFourWidth (2 * s + 1) k) (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k) (sixVertexOddCentralIndex (s + k + 1))) - Real.log 2 + 2 * (∑ j, (sixVertexBetheLogObservable c (sixVertexCanonicalFixedOddDensityPositiveRoots hc s k j) - sixVertexBetheLogObservable c (sixVertexCanonicalOddMidpointHalfRoot hc s k j))) + 2 * (∑ j, (sixVertexBetheLogObservable c (sixVertexCanonicalOddMidpointHalfRoot hc s k j) - sixVertexBetheLogObservable c (sixVertexCanonicalOddLeftHalfRoot hc s k j))) - 2 * ∑ i, sixVertexBetheLogObservable c (sixVertexCanonicalOddBoundaryHalfRoot hc s k i) := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalFixedOddDensityCandidateLogRatio_decomposition hc s k hfixed


-- created on 2026-10-23
