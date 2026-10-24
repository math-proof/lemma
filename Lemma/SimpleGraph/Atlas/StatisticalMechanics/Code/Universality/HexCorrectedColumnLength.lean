import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.HexCorrectedColumnLength
open StatMech StatMech.Universality


/--
[hexEndpoint_unit_depthStep_le_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedColumnLength.lean)
-/
@[path]
private lemma hexEndpoint_unit_depthStep_le_three_eq
  {d : HexReturnCoord}
-- given
  (hd : d.IsUnit) :
-- imply
  2 * d.x - d.y ≤ 3 := by
-- proof
  apply StatMech.Universality.hexEndpoint_unit_depthStep_le_three d hd

/--
[hexEndpointCoordRun_depth_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedColumnLength.lean)
-/
@[path]
private lemma hexEndpointCoordRun_depth_le_eq
  {p d : HexReturnCoord}
  {ts : List ℤ}
-- given
  (hd : d.IsUnit)
  (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
-- imply
  let r := hexEndpointCoordRun p d ts 2 * r.pos.x - r.pos.y ≤ 2 * p.x - p.y + 3 * (ts.length : ℤ) := by
-- proof
  apply StatMech.Universality.hexEndpointCoordRun_depth_le p d ts hd hlegal

/--
[hexEndpointCoordRun_depth_le_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedColumnLength.lean)
-/
@[path]
private lemma hexEndpointCoordRun_depth_le_length_eq
  {ts : List ℤ}
-- given
  (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
-- imply
  let r := hexEndpointCoordRun HexReturnCoord.zero HexReturnCoord.base ts 2 * r.pos.x - r.pos.y ≤ 3 * (ts.length : ℤ) := by
-- proof
  apply StatMech.Universality.hexEndpointCoordRun_depth_le_length ts hlegal

/--
[hexAW_three_depth_sub_two_le_returnPos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedColumnLength.lean)
-/
@[path]
private lemma hexAW_three_depth_sub_two_le_returnPos_eq
  {c : HexAWCoord} :
-- imply
  3 * hexAWDepth c - 2 ≤ 2 * (hexAWReturnPos c).x - (hexAWReturnPos c).y := by
-- proof
  apply StatMech.Universality.hexAW_three_depth_sub_two_le_returnPos c

/--
[hexAWDepth_neighbor_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedColumnLength.lean)
-/
@[path]
private lemma hexAWDepth_neighbor_zero_eq
  {c : HexAWCoord} :
-- imply
  hexAWDepth (hexAWNeighbor c 0) = hexAWDepth c := by
-- proof
  apply StatMech.Universality.hexAWDepth_neighbor_zero c

/--
[hexEndpoint_length_ge_of_endsAt_depth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedColumnLength.lean)
-/
@[path]
private lemma hexEndpoint_length_ge_of_endsAt_depth_eq
  {T : ℕ}
  {ts : List ℤ}
  {c : HexAWCoord}
-- given
  (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW)
  (hdepth : hexAWDepth c = T)
  (hend : (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c 0)) :
-- imply
  T ≤ ts.length := by
-- proof
  apply StatMech.Universality.hexEndpoint_length_ge_of_endsAt_depth T ts c hlegal hdepth hend

/--
[hexCSTopWalk_length_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedColumnLength.lean)
-/
@[path]
private lemma hexCSTopWalk_length_ge_eq
  {T L : ℕ}
  {ts : List ℤ}
-- given
  (hT : 0 < T)
  (hwalk : HexCSTopWalk T L hT ts) :
-- imply
  T ≤ (ofTurns hexAWStart 1 ts).endpointNumVertices := by
-- proof
  apply StatMech.Universality.hexCSTopWalk_length_ge T L hT ts hwalk

/--
[hexCSTopWalkAtWidth_length_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedColumnLength.lean)
-/
@[path]
private lemma hexCSTopWalkAtWidth_length_ge_eq
  {T : ℕ}
  {ts : List ℤ}
-- given
  (hT : 0 < T)
  (hwalk : HexCSTopWalkAtWidth T hT ts) :
-- imply
  T ≤ (ofTurns hexAWStart 1 ts).endpointNumVertices := by
-- proof
  apply StatMech.Universality.hexCSTopWalkAtWidth_length_ge T hT ts hwalk


-- created on 2026-10-23
