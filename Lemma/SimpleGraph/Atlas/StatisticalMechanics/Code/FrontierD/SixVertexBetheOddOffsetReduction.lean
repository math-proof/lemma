import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddOffsetReduction.Part3
open Finset Filter Topology StatMech StatMech.FrontierD


/--
[sixVertexFixedChargeRatio_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddOffsetReduction.lean)
-/
@[path]
private lemma sixVertexFixedChargeRatio_zero_eq
  {c : Real}
  {k : Nat}
-- given
  (hc : 0 < c) :
-- imply
  sixVertexFixedChargeRatio c 0 k = 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeRatio_zero hc k

/--
[sixVertexFixedChargeLogRatio_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddOffsetReduction.lean)
-/
@[path]
private lemma sixVertexFixedChargeLogRatio_zero_eq
  {c : Real}
  {k : Nat}
-- given
  (hc : 0 < c) :
-- imply
  sixVertexFixedChargeLogRatio c 0 k = 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeLogRatio_zero hc k

/--
[sixVertexFixedChargeMatchesOffsetFourier_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddOffsetReduction.lean)
-/
@[path]
private lemma sixVertexFixedChargeMatchesOffsetFourier_zero_eq
  {c : Real}
-- given
  (hc : 0 < c) :
-- imply
  SixVertexFixedChargeMatchesOffsetFourier c 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeMatchesOffsetFourier_zero hc

/--
[sixVertexOddChargeBetheCandidateLogRatio_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddOffsetReduction.lean)
-/
@[path]
private lemma sixVertexOddChargeBetheCandidateLogRatio_eq_eq
  {c : Real}
  {r : Nat}
  {k : Nat}
-- given
  (hc : 2 < c)
  (hr : Odd r) :
-- imply
  sixVertexOddChargeBetheCandidateLogRatio hc r k = Real.log (sixVertexZeroPhaseBethePrefactor c (sixVertexFourWidth r k) (sixVertexFixedChargeBetheRoots hc r k) (sixVertexFixedChargeBetheCentralIndex r k)) + ∑ j ∈ (Finset.univ.erase (sixVertexFixedChargeBetheCentralIndex r k)), Real.log ‖sixVertexBetheM c (sixVertexBethePhase (sixVertexFixedChargeBetheRoots hc r k j))‖ - (Real.log 2 + 2 * ∑ j, Real.log ‖sixVertexBetheM c (sixVertexBethePhase (sixVertexPositiveHalfBetheRoots hc (r + k) j))‖) := by
-- proof
  apply StatMech.FrontierD.sixVertexOddChargeBetheCandidateLogRatio_eq hc hr k

/--
[sixVertexFourWidth_zero_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddOffsetReduction.lean)
-/
@[path]
private lemma sixVertexFourWidth_zero_add_eq
  {r k : Nat} :
-- imply
  sixVertexFourWidth 0 (r + k) = sixVertexFourWidth r k := by
-- proof
  apply StatMech.FrontierD.sixVertexFourWidth_zero_add r k

/--
[sixVertexHalfFilledCandidateValue_eq_sameWidthCentralPerron](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddOffsetReduction.lean)
-/
@[path]
private lemma sixVertexHalfFilledCandidateValue_eq_sameWidthCentralPerron_eq
  {c : Real}
  {r k : Nat}
-- given
  (hc : 2 < c)
  (hhalf : SixVertexHasSymmetricBetheIdentification c (sixVertexPositiveHalfBetheRootFamily hc)) :
-- imply
  sixVertexSymmetricBetheEigenvalueValue c (sixVertexPositiveHalfBetheRoots hc (r + k)) = sixVertexLambda (sixVertexFourWidth r k) 0 (sixVertexFourWidth_even r k) (Nat.zero_le _) c := by
-- proof
  apply StatMech.FrontierD.sixVertexHalfFilledCandidateValue_eq_sameWidthCentralPerron hc r k hhalf

/--
[sixVertexFixedChargeLogRatio_eq_oddBetheCandidate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddOffsetReduction.lean)
-/
@[path]
private lemma sixVertexFixedChargeLogRatio_eq_oddBetheCandidate_eq
  {c : Real}
  {r : Nat}
  {k : Nat}
-- given
  (hc : 2 < c)
  (hhalf : SixVertexHasSymmetricBetheIdentification c (sixVertexPositiveHalfBetheRootFamily hc))
  (hodd : SixVertexOddChargeBethePerronIdentification c r) :
-- imply
  sixVertexFixedChargeLogRatio c r k = sixVertexOddChargeBetheCandidateLogRatio hc r k := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeLogRatio_eq_oddBetheCandidate hc k hhalf hodd

/--
[sixVertexFixedChargeMatchesOffsetFourier_iff_oddBetheCandidate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddOffsetReduction.lean)
-/
@[path]
private lemma sixVertexFixedChargeMatchesOffsetFourier_iff_oddBetheCandidate_eq
  {c : Real}
  {r : Nat}
-- given
  (hc : 2 < c)
  (hhalf : SixVertexHasSymmetricBetheIdentification c (sixVertexPositiveHalfBetheRootFamily hc))
  (hodd : SixVertexOddChargeBethePerronIdentification c r) :
-- imply
  SixVertexFixedChargeMatchesOffsetFourier c r ↔ SixVertexOddChargeBetheCandidateMatchesOffsetFourier hc r := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeMatchesOffsetFourier_iff_oddBetheCandidate hc hhalf hodd


-- created on 2026-10-23
