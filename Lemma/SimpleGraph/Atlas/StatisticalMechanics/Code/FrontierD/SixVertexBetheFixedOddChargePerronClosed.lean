import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedOddChargePerronClosed.Part2
open Filter Topology StatMech StatMech.FrontierD


/--
[sixVertexFixedOddChargeBetheEigenvalueValue_reindex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedOddChargePerronClosed.lean)
-/
@[path]
private lemma sixVertexFixedOddChargeBetheEigenvalueValue_reindex_eq
  {c : Real}
  {s k : Nat}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexZeroPhaseBetheEigenvalueValue c (sixVertexFourWidth (2 * s + 1) k) (sixVertexFixedOddChargeBetheRoots hc s k) (sixVertexOddCentralIndex (s + k + 1)) = sixVertexFixedOddChargeBetheEigenvalueValue hc (2 * s + 1) k := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedOddChargeBetheEigenvalueValue_reindex hc s k

/--
[sixVertexEventuallyOddChargeBethePerronIdentification_of_densityTail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedOddChargePerronClosed.lean)
-/
@[path]
private lemma sixVertexEventuallyOddChargeBethePerronIdentification_of_densityTail_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c) :
-- imply
  ∀ᶠ k : Nat in atTop, sixVertexFixedOddChargeBetheEigenvalueValue hc (2 * s + 1) k = sixVertexLambdaAlongFour c (2 * s + 1) k := by
-- proof
  apply StatMech.FrontierD.sixVertexEventuallyOddChargeBethePerronIdentification_of_densityTail hc htail s

/--
[sixVertexEventuallySelectedFixedChargeBethePerronIdentification_of_densityTail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedOddChargePerronClosed.lean)
-/
@[path]
private lemma sixVertexEventuallySelectedFixedChargeBethePerronIdentification_of_densityTail_eq
  {c : Real}
  {r : Nat}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c) :
-- imply
  ∀ᶠ k : Nat in atTop, sixVertexSelectedFixedChargeBetheEigenvalueValue hc r k = sixVertexLambdaAlongFour c r k := by
-- proof
  apply StatMech.FrontierD.sixVertexEventuallySelectedFixedChargeBethePerronIdentification_of_densityTail hc htail r


-- created on 2026-10-23
