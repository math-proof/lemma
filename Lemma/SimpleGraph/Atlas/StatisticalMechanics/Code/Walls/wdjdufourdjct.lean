import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.wdjdufourdjct.Part4
open Finset Set SimpleGraph StatMech StatMech.Lattice


/--
[wdj_dufourdFig1_chi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wdjdufourdjct.lean)
-/
@[path]
private lemma wdj_dufourdFig1_chi_eq :
-- imply
  wdj_dufourdFig1.wdj_ec = 4 := by
-- proof
  apply StatMech.Lattice.wdj_dufourdFig1_chi

/--
[wdj_dufourdFig1_genus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wdjdufourdjct.lean)
-/
@[path]
private lemma wdj_dufourdFig1_genus_eq :
-- imply
  wdj_dufourdFig1.wdj_genus = 1 := by
-- proof
  apply StatMech.Lattice.wdj_dufourdFig1_genus

/--
[wdj_dufourdFig1_not_planar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wdjdufourdjct.lean)
-/
@[path]
private lemma wdj_dufourdFig1_not_planar_eq :
-- imply
  ¬ wdj_dufourdFig1.wdj_planar := by
-- proof
  apply StatMech.Lattice.wdj_dufourdFig1_not_planar

/--
[wdj_sphereExample_planar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wdjdufourdjct.lean)
-/
@[path]
private lemma wdj_sphereExample_planar_eq :
-- imply
  wdj_sphereExample.wdj_planar := by
-- proof
  apply StatMech.Lattice.wdj_sphereExample_planar

/--
[wdj_sphereExample_eulerFormula](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wdjdufourdjct.lean)
-/
@[path]
private lemma wdj_sphereExample_eulerFormula_eq :
-- imply
  wdj_sphereExample.wdj_ec = 2 := by
-- proof
  apply StatMech.Lattice.wdj_sphereExample_eulerFormula

/--
[wdj_sphereExample_euler_eq_nc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wdjdufourdjct.lean)
-/
@[path]
private lemma wdj_sphereExample_euler_eq_nc_eq :
-- imply
  wdj_sphereExample.wdj_ec / 2 = wdj_sphereExample.nc := by
-- proof
  apply StatMech.Lattice.wdj_sphereExample_euler_eq_nc

/--
[wdj_JordanIncrement_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wdjdufourdjct.lean)
-/
@[path]
private lemma wdj_JordanIncrement_witness_eq :
-- imply
  wdj_JordanIncrement ⟨15, 7, 6, 6, 3⟩ ⟨15, 7, 7, 5, 4⟩ := by
-- proof
  apply StatMech.Lattice.wdj_JordanIncrement_witness

/--
[wdj_JordanIncrement_iff_nc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wdjdufourdjct.lean)
-/
@[path]
private lemma wdj_JordanIncrement_iff_nc_eq
  {before after : wdj_HypermapCounts} :
-- imply
  wdj_JordanIncrement before after ↔ after.nc = before.nc + 1 := by
-- proof
  apply StatMech.Lattice.wdj_JordanIncrement_iff_nc before after

/--
[wdj_revPerm_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wdjdufourdjct.lean)
-/
@[path]
private lemma wdj_revPerm_apply_eq
  {d : Dart} :
-- imply
  wdj_revPerm d = d.rev := by
-- proof
  apply StatMech.Lattice.wdj_revPerm_apply d

/--
[wdj_revPerm_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wdjdufourdjct.lean)
-/
@[path]
private lemma wdj_revPerm_involutive_eq :
-- imply
  wdj_revPerm * wdj_revPerm = 1 := by
-- proof
  apply StatMech.Lattice.wdj_revPerm_involutive

/--
[wdj_dartNext_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wdjdufourdjct.lean)
-/
@[path]
private lemma wdj_dartNext_injective_eq
  {K : Set (Site 2)} :
-- imply
  Function.Injective (dartNextSub K) := by
-- proof
  apply StatMech.Lattice.wdj_dartNext_injective K

/--
[wdj_winding_is_combinatorial_map](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wdjdufourdjct.lean)
-/
@[path]
private lemma wdj_winding_is_combinatorial_map_eq
  {K : Set (Site 2)} :
-- imply
  (wdj_revPerm * wdj_revPerm = 1) ∧ Function.Injective (dartNextSub K) := by
-- proof
  apply StatMech.Lattice.wdj_winding_is_combinatorial_map K

/--
[wdj_ec_shape](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wdjdufourdjct.lean)
-/
@[path]
private lemma wdj_ec_shape_eq
  {K : wdj_HypermapCounts} :
-- imply
  K.wdj_ec = K.nv + K.ne + K.nf - K.nd := by
-- proof
  apply StatMech.Lattice.wdj_ec_shape K

/--
[wdj_orientationConsistent_beyond_increment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wdjdufourdjct.lean)
-/
@[path]
private lemma wdj_orientationConsistent_beyond_increment_eq :
-- imply
  ∃ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a), ¬ wel_OrientationConsistent (![1, 1] : Site 2) Vc := by
-- proof
  apply StatMech.Lattice.wdj_orientationConsistent_beyond_increment

/--
[wdj_windingWall_residue_is_orientation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wdjdufourdjct.lean)
-/
@[path]
private lemma wdj_windingWall_residue_is_orientation_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (hOriented : ∀ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a), wel_OrientationConsistent (![1, 1] : Site 2) Vc → wos_SignsAlternateInColumnOrder (![1, 1] : Site 2) Vc)
  (h : wel_OrientationConsistent (![1, 1] : Site 2) Vc) :
-- imply
  wos_SignsAlternateInColumnOrder (![1, 1] : Site 2) Vc := by
-- proof
  apply StatMech.Lattice.wdj_windingWall_residue_is_orientation hOriented Vc h


-- created on 2026-10-23
