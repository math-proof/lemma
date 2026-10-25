import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedHighestCut.Part3
open StatMech StatMech.Universality StatMech.Universality.HexCSHighestCut


/--
[hexCSPredicateMass_sdiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedHighestCut.lean)
-/
@[path]
private lemma hexCSPredicateMass_sdiff_eq
-- given
  (P Q : List ℤ → Prop)
  (hPQ : ∀ ts, P ts → Q ts)
  (hlegalQ : ∀ ts, Q ts → (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW)
  (hwalk : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE)) :
-- imply
  hexCSPredicateMass Q = hexCSPredicateMass P + hexCSPredicateMass (fun ts => Q ts ∧ ¬ P ts) := by
-- proof
  apply StatMech.Universality.hexCSPredicateMass_sdiff P Q hPQ hlegalQ hwalk

/--
[hexCSInfiniteSideMassAtWidth_sdiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedHighestCut.lean)
-/
@[path]
private lemma hexCSInfiniteSideMassAtWidth_sdiff_eq
  {T : ℕ}
-- given
  (hT : 1 ≤ T)
  (hwalk : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE)) :
-- imply
  hexCSInfiniteSideMassAtWidth (T + 1) - hexCSInfiniteSideMassAtWidth T = hexCSPredicateMass (HexCSNewSideWalk T hT) := by
-- proof
  apply StatMech.Universality.hexCSInfiniteSideMassAtWidth_sdiff T hT hwalk

/--
[hexCSNewSide_tsum_eq_difference](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedHighestCut.lean)
-/
@[path]
private lemma hexCSNewSide_tsum_eq_difference_eq
  {T : ℕ}
-- given
  (hT : 1 ≤ T)
  (hwalk : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE)) :
-- imply
  (∑' d : {ts : List ℤ // HexCSNewSideWalk T hT ts}, hexEndpointSAWwt hexAWStart 1 hexChiE d.1) = hexCSInfiniteSideMassAtWidth (T + 1) - hexCSInfiniteSideMassAtWidth T := by
-- proof
  apply StatMech.Universality.hexCSNewSide_tsum_eq_difference T hT hwalk

/--
[hexCSNextTop_tsum_eq_mass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedHighestCut.lean)
-/
@[path]
private lemma hexCSNextTop_tsum_eq_mass_eq
  {T : ℕ}
-- given
  (hT : 1 ≤ T) :
-- imply
  (∑' b : HexCSNextTopWalk T hT, hexEndpointSAWwt hexAWStart 1 hexChiE b.1) = hexCSInfiniteTopMassAtWidth (T + 1) := by
-- proof
  apply StatMech.Universality.hexCSNextTop_tsum_eq_mass T hT

/--
[recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedHighestCut.lean)
-/
@[path]
private lemma recurrence_eq
  {T : ℕ}
  {hT : 1 ≤ T}
  {H : HexCSHighestCut T hT}
-- given
  (hwalk : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE)) :
-- imply
  hexCSInfiniteSideMassAtWidth (T + 1) - hexCSInfiniteSideMassAtWidth T ≤ hexChiE⁻¹ * (hexCSInfiniteTopMassAtWidth (T + 1)) ^ 2 := by
-- proof
  apply StatMech.Universality.HexCSHighestCut.recurrence H hwalk

/--
[hexCS_highestCuts_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedHighestCut.lean)
-/
@[path]
private lemma hexCS_highestCuts_recurrence_eq
-- given
  (HC : ∀ T (hT : 1 ≤ T), HexCSHighestCut T hT)
  (hwalk : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE)) :
-- imply
  ∀ T, 1 ≤ T → hexCSInfiniteSideMassAtWidth (T + 1) - hexCSInfiniteSideMassAtWidth T ≤ hexChiE⁻¹ * (hexCSInfiniteTopMassAtWidth (T + 1)) ^ 2 := by
-- proof
  apply StatMech.Universality.hexCS_highestCuts_recurrence HC hwalk


-- created on 2026-10-23
