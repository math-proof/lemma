import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripStartReturn
open StatMech StatMech.Universality


/--
[hexCSOutsideStart_eq_neighbor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripStartReturn.lean)
-/
@[path]
private lemma hexCSOutsideStart_eq_neighbor_eq :
-- imply
  hexCSOutsideStartCoord = hexAWNeighbor hexAWOriginCoord 0 := by
-- proof
  apply StatMech.Universality.hexCSOutsideStart_eq_neighbor

/--
[hexCSOutsideStart_mid_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripStartReturn.lean)
-/
@[path]
private lemma hexCSOutsideStart_mid_zero_eq :
-- imply
  hexAWMid hexCSOutsideStartCoord 0 = hexAWStart := by
-- proof
  apply StatMech.Universality.hexCSOutsideStart_mid_zero

/--
[hexCSOutsideStart_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripStartReturn.lean)
-/
@[path]
private lemma hexCSOutsideStart_pos_eq :
-- imply
  hexAWPos hexCSOutsideStartCoord = hexUnit 4 := by
-- proof
  apply StatMech.Universality.hexCSOutsideStart_pos

/--
[hexCSOutsideStart_mid_mem_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripStartReturn.lean)
-/
@[path]
private lemma hexCSOutsideStart_mid_mem_iff_eq
  {T L : ℕ}
  {e : Fin 3}
-- given
  (hT : 0 < T) :
-- imply
  hexAWMid hexCSOutsideStartCoord e ∈ hexCSMids T L ↔ e = 0 := by
-- proof
  apply StatMech.Universality.hexCSOutsideStart_mid_mem_iff T L hT e

/--
[hexCS_endpoint_return_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripStartReturn.lean)
-/
@[path]
private lemma hexCS_endpoint_return_eq_nil_eq
  {T L : ℕ}
  {ts : List ℤ}
-- given
  (hT : 0 < T)
  (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧ (ofTurns hexAWStart 1 ts).StaysIn (hexCSFiniteRegion T L hT).inRegion ∧ (ofTurns hexAWStart 1 ts).EndsAt hexAWStart) :
-- imply
  ts = [] := by
-- proof
  apply StatMech.Universality.hexCS_endpoint_return_eq_nil T L hT ts hadm


-- created on 2026-10-23
