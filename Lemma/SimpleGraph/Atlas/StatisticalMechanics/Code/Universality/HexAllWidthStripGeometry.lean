import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part18
open StatMech StatMech.Universality


/--
[hexAWNeighbor_invol](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWNeighbor_invol_eq
  {c : HexAWCoord}
  {e : Fin 3} :
-- imply
  hexAWNeighbor (hexAWNeighbor c e) e = c := by
-- proof
  apply StatMech.Universality.hexAWNeighbor_invol c e

/--
[hexAWNeighbor_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWNeighbor_ne_eq
  {c : HexAWCoord}
  {e : Fin 3} :
-- imply
  hexAWNeighbor c e ≠ c := by
-- proof
  apply StatMech.Universality.hexAWNeighbor_ne c e

/--
[hexAWPos_neighbor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWPos_neighbor_eq
  {c : HexAWCoord}
  {e : Fin 3} :
-- imply
  hexAWPos (hexAWNeighbor c e) - hexAWPos c = hexUnit (hexAWHeading c e) := by
-- proof
  apply StatMech.Universality.hexAWPos_neighbor c e

/--
[hexAWMid_sub_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWMid_sub_pos_eq
  {c : HexAWCoord}
  {e : Fin 3} :
-- imply
  hexAWMid c e - hexAWPos c = (1 / 2 : ℂ) * hexUnit (hexAWHeading c e) := by
-- proof
  apply StatMech.Universality.hexAWMid_sub_pos c e

/--
[hexAWMid_neighbor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWMid_neighbor_eq
  {c : HexAWCoord}
  {e : Fin 3} :
-- imply
  hexAWMid (hexAWNeighbor c e) e = hexAWMid c e := by
-- proof
  apply StatMech.Universality.hexAWMid_neighbor c e

/--
[hexAWMid_sub_pos_neighbor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWMid_sub_pos_neighbor_eq
  {c : HexAWCoord}
  {e : Fin 3} :
-- imply
  hexAWMid (hexAWNeighbor c e) e - hexAWPos (hexAWNeighbor c e) = -(hexAWMid c e - hexAWPos c) := by
-- proof
  apply StatMech.Universality.hexAWMid_sub_pos_neighbor c e

/--
[hexAWInStrip_mem_coordBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWInStrip_mem_coordBox_eq
  {T L : ℕ}
  {c : HexAWCoord}
-- given
  (hc : hexAWInStrip T L c) :
-- imply
  c ∈ hexAWCoordBox T L := by
-- proof
  apply StatMech.Universality.hexAWInStrip_mem_coordBox T L c hc

/--
[hexAW_mem_vertexSet_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAW_mem_vertexSet_iff_eq
  {T L : ℕ}
  {c : HexAWCoord} :
-- imply
  c ∈ hexAWVertexSet T L ↔ hexAWInStrip T L c := by
-- proof
  apply StatMech.Universality.hexAW_mem_vertexSet_iff T L c

/--
[hexAWOrigin_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWOrigin_mem_eq
  {T L : ℕ}
-- given
  (hT : 0 < T) :
-- imply
  hexAWOriginCoord ∈ hexAWVertexSet T L := by
-- proof
  apply StatMech.Universality.hexAWOrigin_mem T L hT

/--
[hexAWPos_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWPos_origin_eq :
-- imply
  hexAWPos hexAWOriginCoord = 0 := by
-- proof
  apply StatMech.Universality.hexAWPos_origin

/--
[hexAWMid_origin_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWMid_origin_zero_eq :
-- imply
  hexAWMid hexAWOriginCoord 0 = hexAWStart := by
-- proof
  apply StatMech.Universality.hexAWMid_origin_zero

/--
[hexAWReflectCoord_invol](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWReflectCoord_invol_eq
  {c : HexAWCoord} :
-- imply
  hexAWReflectCoord (hexAWReflectCoord c) = c := by
-- proof
  apply StatMech.Universality.hexAWReflectCoord_invol c

/--
[hexAWReflectEdge_invol](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWReflectEdge_invol_eq
  {e : Fin 3} :
-- imply
  hexAWReflectEdge (hexAWReflectEdge e) = e := by
-- proof
  apply StatMech.Universality.hexAWReflectEdge_invol e

/--
[hexAWReflectEdge_fixed_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWReflectEdge_fixed_iff_eq
  {e : Fin 3} :
-- imply
  hexAWReflectEdge e = e ↔ e = 0 := by
-- proof
  apply StatMech.Universality.hexAWReflectEdge_fixed_iff e

/--
[hexAWLong_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWLong_reflect_eq
  {c : HexAWCoord} :
-- imply
  hexAWLong (hexAWReflectCoord c) = hexAWLong c := by
-- proof
  apply StatMech.Universality.hexAWLong_reflect c

/--
[hexAWTrans_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWTrans_reflect_eq
  {c : HexAWCoord} :
-- imply
  hexAWTrans (hexAWReflectCoord c) = -hexAWTrans c := by
-- proof
  apply StatMech.Universality.hexAWTrans_reflect c

/--
[hexAWDepth_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWDepth_reflect_eq
  {c : HexAWCoord} :
-- imply
  hexAWDepth (hexAWReflectCoord c) = hexAWDepth c := by
-- proof
  apply StatMech.Universality.hexAWDepth_reflect c

/--
[hexAWBookRe2_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWBookRe2_reflect_eq
  {c : HexAWCoord} :
-- imply
  hexAWBookRe2 (hexAWReflectCoord c) = hexAWBookRe2 c := by
-- proof
  apply StatMech.Universality.hexAWBookRe2_reflect c

/--
[hexAWBookSqrt3Im2_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWBookSqrt3Im2_reflect_eq
  {c : HexAWCoord} :
-- imply
  hexAWBookSqrt3Im2 (hexAWReflectCoord c) = -hexAWBookSqrt3Im2 c := by
-- proof
  apply StatMech.Universality.hexAWBookSqrt3Im2_reflect c

/--
[hexAWInStrip_reflect_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWInStrip_reflect_iff_eq
  {T L : ℕ}
  {c : HexAWCoord} :
-- imply
  hexAWInStrip T L (hexAWReflectCoord c) ↔ hexAWInStrip T L c := by
-- proof
  apply StatMech.Universality.hexAWInStrip_reflect_iff T L c

/--
[hexAWCoordBox_reflect_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWCoordBox_reflect_iff_eq
  {T L : ℕ}
  {c : HexAWCoord} :
-- imply
  hexAWReflectCoord c ∈ hexAWCoordBox T L ↔ c ∈ hexAWCoordBox T L := by
-- proof
  apply StatMech.Universality.hexAWCoordBox_reflect_iff T L c

/--
[hexAWVertexSet_reflect_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWVertexSet_reflect_iff_eq
  {T L : ℕ}
  {c : HexAWCoord} :
-- imply
  hexAWReflectCoord c ∈ hexAWVertexSet T L ↔ c ∈ hexAWVertexSet T L := by
-- proof
  apply StatMech.Universality.hexAWVertexSet_reflect_iff T L c

/--
[hexAWReflectCoord_neighbor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWReflectCoord_neighbor_eq
  {c : HexAWCoord}
  {e : Fin 3} :
-- imply
  hexAWReflectCoord (hexAWNeighbor c e) = hexAWNeighbor (hexAWReflectCoord c) (hexAWReflectEdge e) := by
-- proof
  apply StatMech.Universality.hexAWReflectCoord_neighbor c e

/--
[hexAWLinearReflect_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWLinearReflect_four_eq :
-- imply
  (hexUnit 4) ^ 2 * (starRingEnd ℂ) (hexUnit 4) = hexUnit 4 := by
-- proof
  apply StatMech.Universality.hexAWLinearReflect_four

/--
[hexAWLinearReflect_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWLinearReflect_zero_eq :
-- imply
  (hexUnit 4) ^ 2 * (starRingEnd ℂ) (hexUnit 0) = hexUnit 2 := by
-- proof
  apply StatMech.Universality.hexAWLinearReflect_zero

/--
[hexAWLinearReflect_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWLinearReflect_two_eq :
-- imply
  (hexUnit 4) ^ 2 * (starRingEnd ℂ) (hexUnit 2) = hexUnit 0 := by
-- proof
  apply StatMech.Universality.hexAWLinearReflect_two

/--
[hexAWLinearReflect_basisI](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWLinearReflect_basisI_eq :
-- imply
  (hexUnit 4) ^ 2 * (starRingEnd ℂ) hexAWBasisI = hexAWBasisJ := by
-- proof
  apply StatMech.Universality.hexAWLinearReflect_basisI

/--
[hexAWLinearReflect_basisJ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWLinearReflect_basisJ_eq :
-- imply
  (hexUnit 4) ^ 2 * (starRingEnd ℂ) hexAWBasisJ = hexAWBasisI := by
-- proof
  apply StatMech.Universality.hexAWLinearReflect_basisJ

/--
[hexAWLinearReflect_start](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWLinearReflect_start_eq :
-- imply
  (hexUnit 4) ^ 2 * (starRingEnd ℂ) hexAWStart = hexAWStart := by
-- proof
  apply StatMech.Universality.hexAWLinearReflect_start

/--
[hexAWPos_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWPos_reflect_eq
  {c : HexAWCoord} :
-- imply
  hsc_refl hexAWStart 4 (hexAWPos c) = hexAWPos (hexAWReflectCoord c) := by
-- proof
  apply StatMech.Universality.hexAWPos_reflect c

/--
[hexAWRefl_average](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWRefl_average_eq
  {x y : ℂ} :
-- imply
  hsc_refl hexAWStart 4 ((x + y) / 2) = (hsc_refl hexAWStart 4 x + hsc_refl hexAWStart 4 y) / 2 := by
-- proof
  apply StatMech.Universality.hexAWRefl_average x y

/--
[hexAWMid_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWMid_reflect_eq
  {c : HexAWCoord}
  {e : Fin 3} :
-- imply
  hsc_refl hexAWStart 4 (hexAWMid c e) = hexAWMid (hexAWReflectCoord c) (hexAWReflectEdge e) := by
-- proof
  apply StatMech.Universality.hexAWMid_reflect c e

/--
[hexAW_refl_one_eq_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAW_refl_one_eq_four_eq
  {z : ℂ} :
-- imply
  hsc_refl hexAWStart 1 z = hsc_refl hexAWStart 4 z := by
-- proof
  apply StatMech.Universality.hexAW_refl_one_eq_four z

/--
[hexAWMid_reflect_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWMid_reflect_one_eq
  {c : HexAWCoord}
  {e : Fin 3} :
-- imply
  hsc_refl hexAWStart 1 (hexAWMid c e) = hexAWMid (hexAWReflectCoord c) (hexAWReflectEdge e) := by
-- proof
  apply StatMech.Universality.hexAWMid_reflect_one c e

/--
[hexAWReflectVertex_invol](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWReflectVertex_invol_eq
  {T L : ℕ}
  {v : HexAWVertex T L} :
-- imply
  hexAWReflectVertex (hexAWReflectVertex v) = v := by
-- proof
  apply StatMech.Universality.hexAWReflectVertex_invol v

/--
[hexAWStart_mem_mids](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWStart_mem_mids_eq
  {T L : ℕ}
-- given
  (hT : 0 < T) :
-- imply
  hexAWStart ∈ hexAWMids T L := by
-- proof
  apply StatMech.Universality.hexAWStart_mem_mids T L hT

/--
[hexAWFiniteRegion_start](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWFiniteRegion_start_eq
  {T L : ℕ}
-- given
  (hT : 0 < T) :
-- imply
  (hexAWFiniteRegion T L hT).start = hexAWStart := by
-- proof
  apply StatMech.Universality.hexAWFiniteRegion_start T L hT

/--
[hexAWFiniteRegion_mids](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWFiniteRegion_mids_eq
  {T L : ℕ}
-- given
  (hT : 0 < T) :
-- imply
  (hexAWFiniteRegion T L hT).mids = hexAWMids T L := by
-- proof
  apply StatMech.Universality.hexAWFiniteRegion_mids T L hT

/--
[hexAWMids_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWMids_reflect_eq
  {T L : ℕ}
  {z : ℂ}
-- given
  (hz : z ∈ hexAWMids T L) :
-- imply
  hsc_refl hexAWStart 4 z ∈ hexAWMids T L := by
-- proof
  apply StatMech.Universality.hexAWMids_reflect hz

/--
[hexAWFiniteRegion_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWFiniteRegion_reflect_eq
  {T L : ℕ}
  {z : ℂ}
-- given
  (hT : 0 < T)
  (hz : (hexAWFiniteRegion T L hT).inRegion z) :
-- imply
  (hexAWFiniteRegion T L hT).inRegion (hsc_refl hexAWStart 4 z) := by
-- proof
  apply StatMech.Universality.hexAWFiniteRegion_reflect hT z hz

/--
[hexAWFiniteRegion_reflect_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWFiniteRegion_reflect_one_eq
  {T L : ℕ}
  {z : ℂ}
-- given
  (hT : 0 < T)
  (hz : (hexAWFiniteRegion T L hT).inRegion z) :
-- imply
  (hexAWFiniteRegion T L hT).inRegion (hsc_refl hexAWStart 1 z) := by
-- proof
  apply StatMech.Universality.hexAWFiniteRegion_reflect_one hT z hz

/--
[hexAWReflectIncidence_invol](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWReflectIncidence_invol_eq
  {T L : ℕ}
  {e : HexAWIncidence T L} :
-- imply
  hexAWReflectIncidence (hexAWReflectIncidence e) = e := by
-- proof
  apply StatMech.Universality.hexAWReflectIncidence_invol e

/--
[hexAWReflectIncidence_mid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWReflectIncidence_mid_eq
  {T L : ℕ}
  {e : HexAWIncidence T L} :
-- imply
  hexAWMid (hexAWReflectIncidence e).vtx.1 (hexAWReflectIncidence e).edge = hsc_refl hexAWStart 4 (hexAWMid e.vtx.1 e.edge) := by
-- proof
  apply StatMech.Universality.hexAWReflectIncidence_mid e

/--
[hexAWIsInterior_reflect_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWIsInterior_reflect_iff_eq
  {T L : ℕ}
  {e : HexAWIncidence T L} :
-- imply
  hexAWIsInterior (hexAWReflectIncidence e) ↔ hexAWIsInterior e := by
-- proof
  apply StatMech.Universality.hexAWIsInterior_reflect_iff e

/--
[hexAW_mem_incidences](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAW_mem_incidences_eq
  {T L : ℕ}
  {e : HexAWIncidence T L} :
-- imply
  e ∈ hexAWIncidences T L := by
-- proof
  apply StatMech.Universality.hexAW_mem_incidences e

/--
[hexAW_mem_interior_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAW_mem_interior_iff_eq
  {T L : ℕ}
  {e : HexAWIncidence T L} :
-- imply
  e ∈ hexAWInteriorIncidences T L ↔ hexAWIsInterior e := by
-- proof
  apply StatMech.Universality.hexAW_mem_interior_iff e

/--
[hexAW_mem_boundary_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAW_mem_boundary_iff_eq
  {T L : ℕ}
  {e : HexAWIncidence T L} :
-- imply
  e ∈ hexAWBoundaryIncidences T L ↔ ¬ hexAWIsInterior e := by
-- proof
  apply StatMech.Universality.hexAW_mem_boundary_iff e

/--
[hexAWReflectIncidence_mem_interior_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWReflectIncidence_mem_interior_iff_eq
  {T L : ℕ}
  {e : HexAWIncidence T L} :
-- imply
  hexAWReflectIncidence e ∈ hexAWInteriorIncidences T L ↔ e ∈ hexAWInteriorIncidences T L := by
-- proof
  apply StatMech.Universality.hexAWReflectIncidence_mem_interior_iff e

/--
[hexAWReflectIncidence_mem_boundary_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWReflectIncidence_mem_boundary_iff_eq
  {T L : ℕ}
  {e : HexAWIncidence T L} :
-- imply
  hexAWReflectIncidence e ∈ hexAWBoundaryIncidences T L ↔ e ∈ hexAWBoundaryIncidences T L := by
-- proof
  apply StatMech.Universality.hexAWReflectIncidence_mem_boundary_iff e

/--
[hexAW_incidence_partition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAW_incidence_partition_eq
  {T L : ℕ} :
-- imply
  hexAWInteriorIncidences T L ∪ hexAWBoundaryIncidences T L = hexAWIncidences T L := by
-- proof
  apply StatMech.Universality.hexAW_incidence_partition T L

/--
[hexAW_incidence_partition_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAW_incidence_partition_disjoint_eq
  {T L : ℕ} :
-- imply
  Disjoint (hexAWInteriorIncidences T L) (hexAWBoundaryIncidences T L) := by
-- proof
  apply StatMech.Universality.hexAW_incidence_partition_disjoint T L

/--
[hexAWInteriorMate_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWInteriorMate_edge_eq
  {T L : ℕ}
  {e : HexAWInteriorIncidence T L} :
-- imply
  (hexAWInteriorMate e).1.edge = e.1.edge := by
-- proof
  apply StatMech.Universality.hexAWInteriorMate_edge e

/--
[hexAWInteriorMate_vtx](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWInteriorMate_vtx_eq
  {T L : ℕ}
  {e : HexAWInteriorIncidence T L} :
-- imply
  (hexAWInteriorMate e).1.vtx.1 = hexAWNeighbor e.1.vtx.1 e.1.edge := by
-- proof
  apply StatMech.Universality.hexAWInteriorMate_vtx e

/--
[hexAWInteriorMate_invol](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWInteriorMate_invol_eq
  {T L : ℕ}
  {e : HexAWInteriorIncidence T L} :
-- imply
  hexAWInteriorMate (hexAWInteriorMate e) = e := by
-- proof
  apply StatMech.Universality.hexAWInteriorMate_invol e

/--
[hexAWInteriorMate_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWInteriorMate_ne_eq
  {T L : ℕ}
  {e : HexAWInteriorIncidence T L} :
-- imply
  hexAWInteriorMate e ≠ e := by
-- proof
  apply StatMech.Universality.hexAWInteriorMate_ne e

/--
[hexAWInteriorMate_mid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWInteriorMate_mid_eq
  {T L : ℕ}
  {e : HexAWInteriorIncidence T L} :
-- imply
  hexAWMid (hexAWInteriorMate e).1.vtx.1 (hexAWInteriorMate e).1.edge = hexAWMid e.1.vtx.1 e.1.edge := by
-- proof
  apply StatMech.Universality.hexAWInteriorMate_mid e

/--
[hexAWInteriorMate_opposite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWInteriorMate_opposite_eq
  {T L : ℕ}
  {e : HexAWInteriorIncidence T L} :
-- imply
  hexAWMid (hexAWInteriorMate e).1.vtx.1 (hexAWInteriorMate e).1.edge - hexAWPos (hexAWInteriorMate e).1.vtx.1 = -(hexAWMid e.1.vtx.1 e.1.edge - hexAWPos e.1.vtx.1) := by
-- proof
  apply StatMech.Universality.hexAWInteriorMate_opposite e

/--
[hexAWPairIncidence_eq_mate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWPairIncidence_eq_mate_eq
  {T L : ℕ}
  {e : HexAWIncidence T L}
-- given
  (he : hexAWIsInterior e) :
-- imply
  hexAWPairIncidence e = (hexAWInteriorMate ⟨e, he⟩).1 := by
-- proof
  apply StatMech.Universality.hexAWPairIncidence_eq_mate e he

/--
[hexAWInteriorPairingOfDomain_interior_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWInteriorPairingOfDomain_interior_sub_eq
  {T L : ℕ}
  {D : HexDomain (HexAWVertex T L)}
-- given
  (hpos : ∀ v, D.pos v = hexAWPos v.1)
  (hmid : ∀ v e, D.mid v e = hexAWMid v.1 e)
  (hvertices : ∀ v, v ∈ D.interiorVertices) :
-- imply
  (hexAWInteriorPairingOfDomain D hpos hmid).interior ⊆ D.incidences := by
-- proof
  apply StatMech.Universality.hexAWInteriorPairingOfDomain_interior_sub D hpos hmid hvertices

/--
[hexAWStartIncidence_mid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWStartIncidence_mid_eq
  {T L : ℕ}
-- given
  (hT : 0 < T) :
-- imply
  hexAWMid (hexAWStartIncidence T L hT).vtx.1 (hexAWStartIncidence T L hT).edge = hexAWStart := by
-- proof
  apply StatMech.Universality.hexAWStartIncidence_mid T L hT

/--
[hexAWStartIncidence_heading](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWStartIncidence_heading_eq
  {T L : ℕ}
-- given
  (hT : 0 < T) :
-- imply
  hexAWHeading (hexAWStartIncidence T L hT).vtx.1 (hexAWStartIncidence T L hT).edge = 4 := by
-- proof
  apply StatMech.Universality.hexAWStartIncidence_heading T L hT

/--
[hexAWStartIncidence_mem_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWStartIncidence_mem_boundary_eq
  {T L : ℕ}
-- given
  (hT : 0 < T) :
-- imply
  hexAWStartIncidence T L hT ∈ hexAWBoundaryIncidences T L := by
-- proof
  apply StatMech.Universality.hexAWStartIncidence_mem_boundary T L hT

/--
[hexAWStartIncidence_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWStartIncidence_reflect_eq
  {T L : ℕ}
-- given
  (hT : 0 < T) :
-- imply
  hexAWReflectIncidence (hexAWStartIncidence T L hT) = hexAWStartIncidence T L hT := by
-- proof
  apply StatMech.Universality.hexAWStartIncidence_reflect T L hT

/--
[hexAWReflectIncidence_fixed_shape](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWReflectIncidence_fixed_shape_eq
  {T L : ℕ}
  {e : HexAWIncidence T L}
-- given
  (he : hexAWReflectIncidence e = e) :
-- imply
  e.vtx.1.i = e.vtx.1.j ∧ e.edge = 0 := by
-- proof
  apply StatMech.Universality.hexAWReflectIncidence_fixed_shape e he

/--
[hexAW_fixed_boundary_classification](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAW_fixed_boundary_classification_eq
  {T L : ℕ}
  {e : HexAWIncidence T L}
-- given
  (heBoundary : e ∈ hexAWBoundaryIncidences T L)
  (heFixed : hexAWReflectIncidence e = e) :
-- imply
  (e.vtx.1 = hexAWOriginCoord ∧ e.edge = 0) ∨ ∃ k : ℕ, T = 2 * k ∧ e.vtx.1 = hexAWRightFixedCoord k ∧ e.edge = 0 := by
-- proof
  apply StatMech.Universality.hexAW_fixed_boundary_classification e heBoundary heFixed

/--
[hexAWRightFixedCoord_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWRightFixedCoord_mem_eq
  {k L : ℕ}
-- given
  (hk : 0 < k) :
-- imply
  hexAWRightFixedCoord k ∈ hexAWVertexSet (2 * k) L := by
-- proof
  apply StatMech.Universality.hexAWRightFixedCoord_mem k L hk

/--
[hexAWRightFixedIncidence_mem_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWRightFixedIncidence_mem_boundary_eq
  {k L : ℕ}
-- given
  (hk : 0 < k) :
-- imply
  hexAWRightFixedIncidence k L hk ∈ hexAWBoundaryIncidences (2 * k) L := by
-- proof
  apply StatMech.Universality.hexAWRightFixedIncidence_mem_boundary k L hk

/--
[hexAWRightFixedIncidence_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean)
-/
@[path]
private lemma hexAWRightFixedIncidence_reflect_eq
  {k L : ℕ}
-- given
  (hk : 0 < k) :
-- imply
  hexAWReflectIncidence (hexAWRightFixedIncidence k L hk) = hexAWRightFixedIncidence k L hk := by
-- proof
  apply StatMech.Universality.hexAWRightFixedIncidence_reflect k L hk


-- created on 2026-10-23
