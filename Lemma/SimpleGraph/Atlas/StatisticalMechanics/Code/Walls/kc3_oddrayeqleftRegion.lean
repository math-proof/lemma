import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.kc3_oddrayeqleftRegion
open Set SimpleGraph Function StatMech StatMech.Walls


/--
[kc3_leftRegion_eq_oddRay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_oddrayeqleftRegion.lean)
-/
@[path]
private lemma kc3_leftRegion_eq_oddRay_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a} :
-- imply
  jec_leftRegion Vc = {z : Site 2 | ¬ Even (jec_rayCount z Vc)} := by
-- proof
  apply StatMech.Walls.kc3_leftRegion_eq_oddRay Vc

/--
[kc3_mem_leftRegion_iff_oddRay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_oddrayeqleftRegion.lean)
-/
@[path]
private lemma kc3_mem_leftRegion_iff_oddRay_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2} :
-- imply
  z ∈ jec_leftRegion Vc ↔ ¬ Even (jec_rayCount z Vc) := by
-- proof
  apply StatMech.Walls.kc3_mem_leftRegion_iff_oddRay Vc z

/--
[kc3_evenRay_iff_not_mem_leftRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_oddrayeqleftRegion.lean)
-/
@[path]
private lemma kc3_evenRay_iff_not_mem_leftRegion_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2} :
-- imply
  Even (jec_rayCount z Vc) ↔ z ∉ jec_leftRegion Vc := by
-- proof
  apply StatMech.Walls.kc3_evenRay_iff_not_mem_leftRegion Vc z

/--
[kc3_mem_orbitLeftRegion_iff_oddRay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_oddrayeqleftRegion.lean)
-/
@[path]
private lemma kc3_mem_orbitLeftRegion_iff_oddRay_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {z : Site 2} :
-- imply
  z ∈ jec_leftRegion (mpl_orbitLoop K a) ↔ ¬ Even (jec_rayCount z (mpl_orbitLoop K a)) := by
-- proof
  apply StatMech.Walls.kc3_mem_orbitLeftRegion_iff_oddRay K a z

/--
[kc3_supportOddInK_iff_leftRegion_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_oddrayeqleftRegion.lean)
-/
@[path]
private lemma kc3_supportOddInK_iff_leftRegion_subset_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  exc_SupportOddInK K a ↔ kc3_LeftRegionSupportSubset K a := by
-- proof
  apply StatMech.Walls.kc3_supportOddInK_iff_leftRegion_subset

/--
[kc3_supportOddInK_of_leftRegion_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_oddrayeqleftRegion.lean)
-/
@[path]
private lemma kc3_supportOddInK_of_leftRegion_subset_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (h : kc3_LeftRegionSupportSubset K a) :
-- imply
  exc_SupportOddInK K a := by
-- proof
  apply StatMech.Walls.kc3_supportOddInK_of_leftRegion_subset h

/--
[kc3_leftRegion_subset_of_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_oddrayeqleftRegion.lean)
-/
@[path]
private lemma kc3_leftRegion_subset_of_three_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hdown : kc2_DownFaceEven K a)
  (hup : kc2_UpFaceInK K a)
  (hleft : kc2_LeftFaceInK K a) :
-- imply
  kc3_LeftRegionSupportSubset K a := by
-- proof
  apply StatMech.Walls.kc3_leftRegion_subset_of_three hdown hup hleft

/--
[kc3_leftRegion_subset_iff_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_oddrayeqleftRegion.lean)
-/
@[path]
private lemma kc3_leftRegion_subset_iff_three_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  kc3_LeftRegionSupportSubset K a ↔ (kc2_DownFaceEven K a ∧ kc2_UpFaceInK K a ∧ kc2_LeftFaceInK K a) := by
-- proof
  apply StatMech.Walls.kc3_leftRegion_subset_iff_three

/--
[kc3_unitCell_leftRegion_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_oddrayeqleftRegion.lean)
-/
@[path]
private lemma kc3_unitCell_leftRegion_subset_eq :
-- imply
  kc3_LeftRegionSupportSubset unitCell ucBase := by
-- proof
  apply StatMech.Walls.kc3_unitCell_leftRegion_subset


-- created on 2026-10-23
