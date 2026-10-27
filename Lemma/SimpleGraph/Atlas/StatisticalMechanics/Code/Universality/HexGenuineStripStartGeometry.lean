import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.StatisticalMechanics.Code.Universality.HexGenuineStripStartGeometry.Part4
open StatMech StatMech.Universality


/--
[hexGenuineStrip_vertex_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripStartGeometry.lean)
-/
@[path]
private lemma hexGenuineStrip_vertex_eq_zero_eq
  {v : Fin 1} :
-- imply
  v = 0 := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_vertex_eq_zero v

/--
[hexGenuineStrip_incidences](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripStartGeometry.lean)
-/
@[path]
private lemma hexGenuineStrip_incidences_eq :
-- imply
  hexGenuineStripDomain.incidences = {hexGenuineStripIncA, hexGenuineStripIncU, hexGenuineStripIncTp} := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_incidences

/--
[hexGenuineStrip_boundaryIncidences](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripStartGeometry.lean)
-/
@[path]
private lemma hexGenuineStrip_boundaryIncidences_eq :
-- imply
  hexGenuineStripDomain.incidences \ hexGenuineStripPairing.interior = {hexGenuineStripIncA, hexGenuineStripIncU, hexGenuineStripIncTp} := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_boundaryIncidences

/--
[hexGenuineStrip_mid_A](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripStartGeometry.lean)
-/
@[path]
private lemma hexGenuineStrip_mid_A_eq :
-- imply
  hexGenuineStripDomain.mid hexGenuineStripIncA.vtx hexGenuineStripIncA.edge = hexGenuineStripStart := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_mid_A

/--
[hexGenuineStrip_mid_U](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripStartGeometry.lean)
-/
@[path]
private lemma hexGenuineStrip_mid_U_eq :
-- imply
  hexGenuineStripDomain.mid hexGenuineStripIncU.vtx hexGenuineStripIncU.edge = hexConcreteQ hexGenuineStripStart 1 := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_mid_U

/--
[hexGenuineStrip_mid_Tp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripStartGeometry.lean)
-/
@[path]
private lemma hexGenuineStrip_mid_Tp_eq :
-- imply
  hexGenuineStripDomain.mid hexGenuineStripIncTp.vtx hexGenuineStripIncTp.edge = hexConcreteR hexGenuineStripStart 1 := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_mid_Tp

/--
[hexGenuineStrip_hgeom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripStartGeometry.lean)
-/
@[path]
private lemma hexGenuineStrip_hgeom_eq
  {v : Fin 1}
  {j : Fin 3} :
-- imply
  hexGenuineStripDomain.mid v j - hexGenuineStripDomain.pos v = (1 / 2 : ℂ) * hexUnit (hexGenuineStripHeading v j) := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_hgeom v j

/--
[hexGenuineStrip_start_eq_halfStep_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripStartGeometry.lean)
-/
@[path]
private lemma hexGenuineStrip_start_eq_halfStep_four_eq :
-- imply
  hexGenuineStripStart = halfStep 4 := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_start_eq_halfStep_four

/--
[hexGenuineStrip_mid_U_eq_halfStep_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripStartGeometry.lean)
-/
@[path]
private lemma hexGenuineStrip_mid_U_eq_halfStep_zero_eq :
-- imply
  hexConcreteQ hexGenuineStripStart 1 = halfStep 0 := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_mid_U_eq_halfStep_zero

/--
[hexGenuineStrip_mid_Tp_eq_halfStep_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripStartGeometry.lean)
-/
@[path]
private lemma hexGenuineStrip_mid_Tp_eq_halfStep_two_eq :
-- imply
  hexConcreteR hexGenuineStripStart 1 = halfStep 2 := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_mid_Tp_eq_halfStep_two

/--
[hexGenuineStrip_halfStep_zero_re](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripStartGeometry.lean)
-/
@[path]
private lemma hexGenuineStrip_halfStep_zero_re_eq :
-- imply
  (halfStep 0).re = Real.sqrt 3 / 4 := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_halfStep_zero_re

/--
[hexGenuineStrip_halfStep_two_re](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripStartGeometry.lean)
-/
@[path]
private lemma hexGenuineStrip_halfStep_two_re_eq :
-- imply
  (halfStep 2).re = -(Real.sqrt 3 / 4) := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_halfStep_two_re

/--
[hexGenuineStrip_halfStep_two_im](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripStartGeometry.lean)
-/
@[path]
private lemma hexGenuineStrip_halfStep_two_im_eq :
-- imply
  (halfStep 2).im = 1 / 4 := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_halfStep_two_im

/--
[hexGenuineStripCoordinateRegion_start](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripStartGeometry.lean)
-/
@[path]
private lemma hexGenuineStripCoordinateRegion_start_eq :
-- imply
  hexGenuineStripCoordinateRegion.start = hexGenuineStripRegion.start := by
-- proof
  apply StatMech.Universality.hexGenuineStripCoordinateRegion_start

/--
[hexGenuineStrip_cls_A](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripStartGeometry.lean)
-/
@[path]
private lemma hexGenuineStrip_cls_A_eq :
-- imply
  hexRegionClsInc hexGenuineStripCoordinateRegion hexGenuineStripDomain hexGenuineStripIncA = 0 := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_cls_A

/--
[hexGenuineStrip_cls_U](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripStartGeometry.lean)
-/
@[path]
private lemma hexGenuineStrip_cls_U_eq :
-- imply
  hexRegionClsInc hexGenuineStripCoordinateRegion hexGenuineStripDomain hexGenuineStripIncU = 4 := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_cls_U

/--
[hexGenuineStrip_cls_Tp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripStartGeometry.lean)
-/
@[path]
private lemma hexGenuineStrip_cls_Tp_eq :
-- imply
  hexRegionClsInc hexGenuineStripCoordinateRegion hexGenuineStripDomain hexGenuineStripIncTp = 2 := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_cls_Tp

/--
[hexGenuineStrip_class_zero_iff_start](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripStartGeometry.lean)
-/
@[path]
private lemma hexGenuineStrip_class_zero_iff_start_eq
  {e : HexIncidence (Fin 1)}
-- given
  (he : e ∈ hexGenuineStripDomain.incidences \ hexGenuineStripPairing.interior) :
-- imply
  hexRegionClsInc hexGenuineStripCoordinateRegion hexGenuineStripDomain e = 0 ↔ hexGenuineStripDomain.mid e.vtx e.edge = hexGenuineStripRegion.start := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_class_zero_iff_start e he

/--
[hexGenuineStrip_startFiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripStartGeometry.lean)
-/
@[path]
private lemma hexGenuineStrip_startFiber_eq :
-- imply
  (hexGenuineStripDomain.incidences \ hexGenuineStripPairing.interior).filter (fun e => hexRegionClsInc hexGenuineStripCoordinateRegion hexGenuineStripDomain e = 0) = {hexGenuineStripIncA} := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_startFiber

/--
[hexGenuineStrip_LFiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripStartGeometry.lean)
-/
@[path]
private lemma hexGenuineStrip_LFiber_eq :
-- imply
  (hexGenuineStripDomain.incidences \ hexGenuineStripPairing.interior).filter (fun e => hexRegionClsInc hexGenuineStripCoordinateRegion hexGenuineStripDomain e = 1) = ∅ := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_LFiber

/--
[hexGenuineStrip_TpFiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripStartGeometry.lean)
-/
@[path]
private lemma hexGenuineStrip_TpFiber_eq :
-- imply
  (hexGenuineStripDomain.incidences \ hexGenuineStripPairing.interior).filter (fun e => hexRegionClsInc hexGenuineStripCoordinateRegion hexGenuineStripDomain e = 2) = {hexGenuineStripIncTp} := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_TpFiber

/--
[hexGenuineStrip_TmFiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripStartGeometry.lean)
-/
@[path]
private lemma hexGenuineStrip_TmFiber_eq :
-- imply
  (hexGenuineStripDomain.incidences \ hexGenuineStripPairing.interior).filter (fun e => hexRegionClsInc hexGenuineStripCoordinateRegion hexGenuineStripDomain e = 3) = ∅ := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_TmFiber

/--
[hexGenuineStrip_UFiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripStartGeometry.lean)
-/
@[path]
private lemma hexGenuineStrip_UFiber_eq :
-- imply
  (hexGenuineStripDomain.incidences \ hexGenuineStripPairing.interior).filter (fun e => hexRegionClsInc hexGenuineStripCoordinateRegion hexGenuineStripDomain e = 4) = {hexGenuineStripIncU} := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_UFiber

/--
[hexGenuineStrip_mid_complete](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripStartGeometry.lean)
-/
@[path]
private lemma hexGenuineStrip_mid_complete_eq
  {m : ℂ}
-- given
  (hm : m ∈ hexGenuineStripRegion.mids) :
-- imply
  ∃ e ∈ hexGenuineStripDomain.incidences \ hexGenuineStripPairing.interior, hexGenuineStripDomain.mid e.vtx e.edge = m := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_mid_complete m hm

/--
[hexGenuineStrip_boundary_mid_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripStartGeometry.lean)
-/
@[path]
private lemma hexGenuineStrip_boundary_mid_injective_eq
  {e₁ : HexIncidence (Fin 1)}
  {e₂ : HexIncidence (Fin 1)}
-- given
  (he₁ : e₁ ∈ hexGenuineStripDomain.incidences \ hexGenuineStripPairing.interior)
  (he₂ : e₂ ∈ hexGenuineStripDomain.incidences \ hexGenuineStripPairing.interior)
  (hmid : hexGenuineStripDomain.mid e₁.vtx e₁.edge = hexGenuineStripDomain.mid e₂.vtx e₂.edge) :
-- imply
  e₁ = e₂ := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_boundary_mid_injective e₁ he₁ e₂ he₂ hmid

/--
[hexGenuineStrip_existsUnique_boundary_incidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripStartGeometry.lean)
-/
@[path]
private lemma hexGenuineStrip_existsUnique_boundary_incidence_eq
  {m : ℂ}
-- given
  (hm : m ∈ hexGenuineStripRegion.mids) :
-- imply
  ∃! e : HexIncidence (Fin 1), e ∈ hexGenuineStripDomain.incidences \ hexGenuineStripPairing.interior ∧ hexGenuineStripDomain.mid e.vtx e.edge = m := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_existsUnique_boundary_incidence m hm


-- created on 2026-10-23
