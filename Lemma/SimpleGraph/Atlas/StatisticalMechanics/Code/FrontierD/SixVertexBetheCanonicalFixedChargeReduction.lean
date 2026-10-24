import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedChargeReduction
open Filter Topology StatMech StatMech.FrontierD


/--
[sixVertexEventuallyFixedChargeBethePerronIdentification_of_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedChargeReduction.lean)
-/
@[path]
private lemma sixVertexEventuallyFixedChargeBethePerronIdentification_of_even_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c)
  (h : SixVertexEventuallyEvenChargeBethePerronIdentification hc s) :
-- imply
  SixVertexEventuallyFixedChargeBethePerronIdentification hc (2 * s) := by
-- proof
  apply StatMech.FrontierD.sixVertexEventuallyFixedChargeBethePerronIdentification_of_even hc s h

/--
[sixVertexEventuallyFixedChargeBethePerronIdentification_of_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedChargeReduction.lean)
-/
@[path]
private lemma sixVertexEventuallyFixedChargeBethePerronIdentification_of_odd_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c)
  (h : ∀ᶠ k : Nat in atTop, sixVertexCanonicalFixedOddChargeBetheEigenvalueValue hc s k = sixVertexLambdaAlongFour c (2 * s + 1) k) :
-- imply
  SixVertexEventuallyFixedChargeBethePerronIdentification hc (2 * s + 1) := by
-- proof
  apply StatMech.FrontierD.sixVertexEventuallyFixedChargeBethePerronIdentification_of_odd hc s h

/--
[sixVertexEventuallyFixedChargeBethePerronIdentification](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedChargeReduction.lean)
-/
@[path]
private lemma sixVertexEventuallyFixedChargeBethePerronIdentification_eq
  {c : Real}
  {r : Nat}
-- given
  (hc : 2 < c) :
-- imply
  SixVertexEventuallyFixedChargeBethePerronIdentification hc r := by
-- proof
  apply StatMech.FrontierD.sixVertexEventuallyFixedChargeBethePerronIdentification hc r

/--
[sixVertexFixedChargeLogRatio_eventuallyEq_canonicalBetheCandidate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedChargeReduction.lean)
-/
@[path]
private lemma sixVertexFixedChargeLogRatio_eventuallyEq_canonicalBetheCandidate_eq
  {c : Real}
  {r : Nat}
-- given
  (hc : 2 < c)
  (hfixed : SixVertexEventuallyFixedChargeBethePerronIdentification hc r) :
-- imply
  sixVertexFixedChargeLogRatio c r =ᶠ[atTop] sixVertexCanonicalFixedChargeBetheCandidateLogRatio hc r := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeLogRatio_eventuallyEq_canonicalBetheCandidate hc r hfixed

/--
[sixVertexFixedChargeMatchesOffsetFourier_iff_canonicalBetheCandidate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedChargeReduction.lean)
-/
@[path]
private lemma sixVertexFixedChargeMatchesOffsetFourier_iff_canonicalBetheCandidate_eq
  {c : Real}
  {r : Nat}
-- given
  (hc : 2 < c)
  (hfixed : SixVertexEventuallyFixedChargeBethePerronIdentification hc r) :
-- imply
  SixVertexFixedChargeMatchesOffsetFourier c r ↔ SixVertexCanonicalFixedChargeBetheCandidateMatchesOffsetFourier hc r := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeMatchesOffsetFourier_iff_canonicalBetheCandidate hc r hfixed

/--
[sixVertexAntiferroelectricTransferConclusion_of_canonicalFixedCharge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedChargeReduction.lean)
-/
@[path]
private lemma sixVertexAntiferroelectricTransferConclusion_of_canonicalFixedCharge_eq
  {c : Real}
-- given
  (hc : 2 < c)
  (hbranch : ∀ r : Nat, 1 ≤ r → SixVertexEventuallyFixedChargeBethePerronIdentification hc r)
  (hoffset : ∀ r : Nat, 1 ≤ r → SixVertexCanonicalFixedChargeBetheCandidateMatchesOffsetFourier hc r) :
-- imply
  SixVertexAntiferroelectricTransferConclusion c (sixVertexAntiferroelectricLambda c) := by
-- proof
  apply StatMech.FrontierD.sixVertexAntiferroelectricTransferConclusion_of_canonicalFixedCharge hc hbranch hoffset


-- created on 2026-10-23
