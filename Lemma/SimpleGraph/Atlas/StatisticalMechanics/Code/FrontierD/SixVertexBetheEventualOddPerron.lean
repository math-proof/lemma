import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBetheEventualOddPerron
open Filter Topology StatMech StatMech.FrontierD


/--
[sixVertexEventuallyOddChargeBethePerronIdentification_of_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEventualOddPerron.lean)
-/
@[path]
private lemma sixVertexEventuallyOddChargeBethePerronIdentification_of_all_eq
  {c : Real}
  {r : Nat}
-- given
  (hc : 2 < c)
  (h : SixVertexOddChargeBethePerronIdentification c r) :
-- imply
  SixVertexEventuallyOddChargeBethePerronIdentification hc r := by
-- proof
  apply StatMech.FrontierD.sixVertexEventuallyOddChargeBethePerronIdentification_of_all hc r h

/--
[sixVertexFixedChargeLogRatio_eventuallyEq_oddBetheCandidate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEventualOddPerron.lean)
-/
@[path]
private lemma sixVertexFixedChargeLogRatio_eventuallyEq_oddBetheCandidate_eq
  {c : Real}
  {r : Nat}
-- given
  (hc : 2 < c)
  (hhalf : SixVertexEventuallyHasSymmetricBetheIdentification hc)
  (hodd : SixVertexEventuallyOddChargeBethePerronIdentification hc r) :
-- imply
  sixVertexFixedChargeLogRatio c r =ᶠ[atTop] sixVertexOddChargeBetheCandidateLogRatio hc r := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeLogRatio_eventuallyEq_oddBetheCandidate hc r hhalf hodd

/--
[sixVertexFixedChargeMatchesOffsetFourier_iff_eventualOddBetheCandidate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEventualOddPerron.lean)
-/
@[path]
private lemma sixVertexFixedChargeMatchesOffsetFourier_iff_eventualOddBetheCandidate_eq
  {c : Real}
  {r : Nat}
-- given
  (hc : 2 < c)
  (hhalf : SixVertexEventuallyHasSymmetricBetheIdentification hc)
  (hodd : SixVertexEventuallyOddChargeBethePerronIdentification hc r) :
-- imply
  SixVertexFixedChargeMatchesOffsetFourier c r ↔ SixVertexOddChargeBetheCandidateMatchesOffsetFourier hc r := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeMatchesOffsetFourier_iff_eventualOddBetheCandidate hc r hhalf hodd


-- created on 2026-10-23
