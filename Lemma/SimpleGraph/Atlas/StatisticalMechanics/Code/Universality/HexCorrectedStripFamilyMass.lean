import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripFamilyMass.Part2
open StatMech StatMech.Universality


/--
[hexCS_mem_classIncidences_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripFamilyMass.lean)
-/
@[path]
private lemma hexCS_mem_classIncidences_iff_eq
  {T L : ℕ}
  {hT : 0 < T}
  {cls : HexPairedBoundaryClass}
  {e : HexCSIncidence T L} :
-- imply
  e ∈ hexCSClassIncidences T L hT cls ↔ e ∈ hexCSBoundaryIncidences T L ∧ e ≠ hexCSStartIncidence T L hT ∧ hexCSBoundaryClass e = cls := by
-- proof
  apply StatMech.Universality.hexCS_mem_classIncidences_iff

/--
[hexCS_boundary_mid_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripFamilyMass.lean)
-/
@[path]
private lemma hexCS_boundary_mid_injective_eq
  {T L : ℕ}
  {e f : HexCSIncidence T L}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L)
  (hf : f ∈ hexCSBoundaryIncidences T L)
  (hm : hexAWMid e.vtx.1 e.edge = hexAWMid f.vtx.1 f.edge) :
-- imply
  e = f := by
-- proof
  apply StatMech.Universality.hexCS_boundary_mid_injective he hf hm

/--
[hexCS_class_mid_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripFamilyMass.lean)
-/
@[path]
private lemma hexCS_class_mid_injective_eq
  {T L : ℕ}
  {cls : HexPairedBoundaryClass}
-- given
  (hT : 0 < T) :
-- imply
  Set.InjOn (fun e : HexCSIncidence T L => hexAWMid e.vtx.1 e.edge) (hexCSClassIncidences T L hT cls : Set _) := by
-- proof
  apply StatMech.Universality.hexCS_class_mid_injective T L hT cls

/--
[hexCSLiteralBoundaryMass_eq_incidence_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripFamilyMass.lean)
-/
@[path]
private lemma hexCSLiteralBoundaryMass_eq_incidence_sum_eq
  {T L : ℕ}
  {cls : HexPairedBoundaryClass}
-- given
  (hT : 0 < T) :
-- imply
  hexCSLiteralBoundaryMass T L hT cls = ∑ e ∈ hexCSClassIncidences T L hT cls, endpointCountObservable (hexCSFiniteRegion T L hT).inRegion hexAWStart 1 (hexAWMid e.vtx.1 e.edge) hexChi := by
-- proof
  apply StatMech.Universality.hexCSLiteralBoundaryMass_eq_incidence_sum T L hT cls

/--
[hexCSLiteralBoundaryMass_eq_classWalkMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripFamilyMass.lean)
-/
@[path]
private lemma hexCSLiteralBoundaryMass_eq_classWalkMass_eq
  {T L : ℕ}
  {cls : HexPairedBoundaryClass}
-- given
  (hT : 0 < T) :
-- imply
  hexCSLiteralBoundaryMass T L hT cls = hexCSClassWalkMass T L hT cls := by
-- proof
  apply StatMech.Universality.hexCSLiteralBoundaryMass_eq_classWalkMass T L hT cls

/--
[hexCSA_eq_classWalkMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripFamilyMass.lean)
-/
@[path]
private lemma hexCSA_eq_classWalkMass_eq
  {T L : ℕ}
-- given
  (hT : 0 < T) :
-- imply
  hexCSA T L hT = hexCSClassWalkMass T L hT .side := by
-- proof
  apply StatMech.Universality.hexCSA_eq_classWalkMass T L hT

/--
[hexCSE_eq_classWalkMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripFamilyMass.lean)
-/
@[path]
private lemma hexCSE_eq_classWalkMass_eq
  {T L : ℕ}
-- given
  (hT : 0 < T) :
-- imply
  hexCSE T L hT = hexCSClassWalkMass T L hT .slant := by
-- proof
  apply StatMech.Universality.hexCSE_eq_classWalkMass T L hT

/--
[hexCSB_eq_classWalkMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripFamilyMass.lean)
-/
@[path]
private lemma hexCSB_eq_classWalkMass_eq
  {T L : ℕ}
-- given
  (hT : 0 < T) :
-- imply
  hexCSB T L hT = hexCSClassWalkMass T L hT .top := by
-- proof
  apply StatMech.Universality.hexCSB_eq_classWalkMass T L hT

/--
[hexCS_mem_class_side_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripFamilyMass.lean)
-/
@[path]
private lemma hexCS_mem_class_side_iff_eq
  {T L : ℕ}
  {hT : 0 < T}
  {e : HexCSIncidence T L} :
-- imply
  e ∈ hexCSClassIncidences T L hT .side ↔ e.vtx.1.color = .black ∧ e.edge = 0 ∧ hexAWDepth e.vtx.1 = 0 ∧ hexAWMid e.vtx.1 e.edge ≠ hexAWStart := by
-- proof
  apply StatMech.Universality.hexCS_mem_class_side_iff e

/--
[hexCS_mem_class_top_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripFamilyMass.lean)
-/
@[path]
private lemma hexCS_mem_class_top_iff_eq
  {T L : ℕ}
  {hT : 0 < T}
  {e : HexCSIncidence T L} :
-- imply
  e ∈ hexCSClassIncidences T L hT .top ↔ e.vtx.1.color = .white ∧ e.edge = 0 ∧ hexAWDepth e.vtx.1 = T := by
-- proof
  apply StatMech.Universality.hexCS_mem_class_top_iff e

/--
[hexCS_mem_class_slant_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripFamilyMass.lean)
-/
@[path]
private lemma hexCS_mem_class_slant_iff_eq
  {T L : ℕ}
  {hT : 0 < T}
  {e : HexCSIncidence T L} :
-- imply
  e ∈ hexCSClassIncidences T L hT .slant ↔ e.vtx.1.color = .white ∧ ((e.edge = 1 ∧ e.vtx.1.i = L) ∨ (e.edge = 2 ∧ e.vtx.1.j = L)) := by
-- proof
  apply StatMech.Universality.hexCS_mem_class_slant_iff e

/--
[hexCSClassWalk_side_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripFamilyMass.lean)
-/
@[path]
private lemma hexCSClassWalk_side_iff_eq
  {T L : ℕ}
  {ts : List ℤ}
-- given
  (hT : 0 < T) :
-- imply
  HexCSClassWalk T L hT .side ts ↔ HexCSSideWalk T L hT ts := by
-- proof
  apply StatMech.Universality.hexCSClassWalk_side_iff T L hT ts

/--
[hexCSClassWalk_top_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripFamilyMass.lean)
-/
@[path]
private lemma hexCSClassWalk_top_iff_eq
  {T L : ℕ}
  {ts : List ℤ}
-- given
  (hT : 0 < T) :
-- imply
  HexCSClassWalk T L hT .top ts ↔ HexCSTopWalk T L hT ts := by
-- proof
  apply StatMech.Universality.hexCSClassWalk_top_iff T L hT ts

/--
[hexCSClassWalk_slant_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripFamilyMass.lean)
-/
@[path]
private lemma hexCSClassWalk_slant_iff_eq
  {T L : ℕ}
  {ts : List ℤ}
-- given
  (hT : 0 < T) :
-- imply
  HexCSClassWalk T L hT .slant ts ↔ HexCSSlantWalk T L hT ts := by
-- proof
  apply StatMech.Universality.hexCSClassWalk_slant_iff T L hT ts


-- created on 2026-10-23
