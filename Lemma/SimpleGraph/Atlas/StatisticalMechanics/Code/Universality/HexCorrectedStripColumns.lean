import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.HexCorrectedStripColumns
open StatMech StatMech.Universality


/--
[hexCSTopWalkAtWidth_width_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripColumns.lean)
-/
@[path]
private lemma hexCSTopWalkAtWidth_width_unique_eq
  {T U : ℕ}
  {hT : 0 < T}
  {hU : 0 < U}
  {ts : List ℤ}
-- given
  (hwalkT : HexCSTopWalkAtWidth T hT ts)
  (hwalkU : HexCSTopWalkAtWidth U hU ts) :
-- imply
  T = U := by
-- proof
  apply StatMech.Universality.hexCSTopWalkAtWidth_width_unique hwalkT hwalkU

/--
[hexCSTopWalkWidth_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripColumns.lean)
-/
@[path]
private lemma hexCSTopWalkWidth_pos_eq
  {w : {ts : List ℤ // HexCSTopWalkAnyWidth ts}} :
-- imply
  0 < hexCSTopWalkWidth w := by
-- proof
  apply StatMech.Universality.hexCSTopWalkWidth_pos w

/--
[hexCSTopWalkWidth_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripColumns.lean)
-/
@[path]
private lemma hexCSTopWalkWidth_spec_eq
  {w : {ts : List ℤ // HexCSTopWalkAnyWidth ts}} :
-- imply
  HexCSTopWalkAtWidth (hexCSTopWalkWidth w) (hexCSTopWalkWidth_pos w) w.1 := by
-- proof
  apply StatMech.Universality.hexCSTopWalkWidth_spec w

/--
[hexCSTopWalkWidth_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripColumns.lean)
-/
@[path]
private lemma hexCSTopWalkWidth_eq_eq
  {w : {ts : List ℤ // HexCSTopWalkAnyWidth ts}}
  {T : ℕ}
-- given
  (hT : 0 < T)
  (hw : HexCSTopWalkAtWidth T hT w.1) :
-- imply
  hexCSTopWalkWidth w = T := by
-- proof
  apply StatMech.Universality.hexCSTopWalkWidth_eq w hT hw

/--
[hexCSPredicateMass_eq_tsum_subtype](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripColumns.lean)
-/
@[path]
private lemma hexCSPredicateMass_eq_tsum_subtype_eq
-- given
  (P : List ℤ → Prop) :
-- imply
  hexCSPredicateMass P = ∑' w : {ts : List ℤ // P ts}, hexChiE ^ (ofTurns hexAWStart 1 w.1).endpointNumVertices := by
-- proof
  apply StatMech.Universality.hexCSPredicateMass_eq_tsum_subtype P

/--
[hecd_correctedTop_columnSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripColumns.lean)
-/
@[path]
private lemma hecd_correctedTop_columnSum_eq
  {T : ℕ}
-- given
  (hT : 0 < T) :
-- imply
  hecd_columnSum hexAWStart 1 HexCSTopWalkAnyWidth hexCSTopWalkWidth T = hexCSPredicateMass (HexCSTopWalkAtWidth T hT) := by
-- proof
  apply StatMech.Universality.hecd_correctedTop_columnSum T hT

/--
[hecd_correctedTop_columnSum_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripColumns.lean)
-/
@[path]
private lemma hecd_correctedTop_columnSum_summable_eq
-- given
  (hwalk : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE)) :
-- imply
  Summable (hecd_columnSum hexAWStart 1 HexCSTopWalkAnyWidth hexCSTopWalkWidth) := by
-- proof
  apply StatMech.Universality.hecd_correctedTop_columnSum_summable hwalk


-- created on 2026-10-23
