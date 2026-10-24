import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.AllOpenCoarseBoundaryGeneral
open Finset Set SimpleGraph StatMech StatMech.FrontierA


/--
[bgfdFaithfulAllOpenTrifAt_boundary_witnesses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenCoarseBoundaryGeneral.lean)
-/
@[path]
private lemma bgfdFaithfulAllOpenTrifAt_boundary_witnesses_eq
  {d : ℕ}
  {omega : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {j : Site d}
-- given
  (hR : 1 ≤ R)
  (h : BgfdFaithfulAllOpenTrifAt omega L j)
  (harms : ∀ a : Site d, bc67_GnIncident omega L (bgfdCentre L j) a → (cluster d (removeSites (bc61_boxAround d L (bgfdCentre L j)) omega) a).Infinite → a ∈ box d R) :
-- imply
  ∃ z1 z2 z3 : Site d, z1 ∈ vertexBoundary d R ∧ z2 ∈ vertexBoundary d R ∧ z3 ∈ vertexBoundary d R ∧ bgfdQ omega L z1 ≠ bgfdCentre L j ∧ bgfdQ omega L z2 ≠ bgfdCentre L j ∧ bgfdQ omega L z3 ≠ bgfdCentre L j ∧ (bgfdGraph omega L).Reachable (bgfdCentre L j) (bgfdQ omega L z1) ∧ (bgfdGraph omega L).Reachable (bgfdCentre L j) (bgfdQ omega L z2) ∧ (bgfdGraph omega L).Reachable (bgfdCentre L j) (bgfdQ omega L z3) ∧ ¬ (bkg_deleteVertex (bgfdGraph omega L) (bgfdCentre L j)).Reachable (bgfdQ omega L z1) (bgfdQ omega L z2) ∧ ¬ (bkg_deleteVertex (bgfdGraph omega L) (bgfdCentre L j)).Reachable (bgfdQ omega L z1) (bgfdQ omega L z3) ∧ ¬ (bkg_deleteVertex (bgfdGraph omega L) (bgfdCentre L j)).Reachable (bgfdQ omega L z2) (bgfdQ omega L z3) := by
-- proof
  apply StatMech.FrontierA.bgfdFaithfulAllOpenTrifAt_boundary_witnesses hR h harms

/--
[bgfdFaithfulAllOpenTrifAt_count_le_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenCoarseBoundaryGeneral.lean)
-/
@[path]
private lemma bgfdFaithfulAllOpenTrifAt_count_le_boundary_eq
  {d : ℕ}
  {omega : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {J : Finset (Site d)}
-- given
  (hR : 1 ≤ R)
  (htrif : ∀ j ∈ J, BgfdFaithfulAllOpenTrifAt omega L j)
  (harms : ∀ j ∈ J, ∀ a : Site d, bc67_GnIncident omega L (bgfdCentre L j) a → (cluster d (removeSites (bc61_boxAround d L (bgfdCentre L j)) omega) a).Infinite → a ∈ box d R) :
-- imply
  J.card ≤ (vertexBoundary_finite d R).toFinset.card := by
-- proof
  apply StatMech.FrontierA.bgfdFaithfulAllOpenTrifAt_count_le_boundary omega L R hR J htrif harms

/--
[bgfd_gnIncident_arm_mem_outer_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenCoarseBoundaryGeneral.lean)
-/
@[path]
private lemma bgfd_gnIncident_arm_mem_outer_box_eq
  {d : ℕ}
  {omega : ConfigSpace (Sym2 (Site d))}
  {L N : ℕ}
  {j a : Site d}
-- given
  (hc : bgfdCentre L j ∈ box d N)
  (hi : bc67_GnIncident omega L (bgfdCentre L j) a) :
-- imply
  a ∈ box d (N + L + 1) := by
-- proof
  apply StatMech.FrontierA.bgfd_gnIncident_arm_mem_outer_box hc hi

/--
[bgfdFaithfulAllOpenTrifAt_count_inner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenCoarseBoundaryGeneral.lean)
-/
@[path]
private lemma bgfdFaithfulAllOpenTrifAt_count_inner_eq
  {d : ℕ}
  {omega : ConfigSpace (Sym2 (Site d))}
  {L N : ℕ}
  {J : Finset (Site d)}
-- given
  (htrif : ∀ j ∈ J, BgfdFaithfulAllOpenTrifAt omega L j)
  (hcenter : ∀ j ∈ J, bgfdCentre L j ∈ box d N) :
-- imply
  J.card ≤ (vertexBoundary_finite d (N + L + 1)).toFinset.card := by
-- proof
  apply StatMech.FrontierA.bgfdFaithfulAllOpenTrifAt_count_inner omega L N J htrif hcenter

/--
[bgfd_centre_mem_scaled_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenCoarseBoundaryGeneral.lean)
-/
@[path]
private lemma bgfd_centre_mem_scaled_box_eq
  {d : ℕ}
  {L N : ℕ}
  {j : Site d}
-- given
  (hj : j ∈ box d N) :
-- imply
  bgfdCentre L j ∈ box d ((2 * L + 1) * N) := by
-- proof
  apply StatMech.FrontierA.bgfd_centre_mem_scaled_box hj

/--
[mem_bgfdFaithfulAllOpenTrifIndicesInBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenCoarseBoundaryGeneral.lean)
-/
@[path]
private lemma mem_bgfdFaithfulAllOpenTrifIndicesInBox_eq
  {d : ℕ}
  {omega : ConfigSpace (Sym2 (Site d))}
  {L N : ℕ}
  {j : Site d} :
-- imply
  j ∈ bgfdFaithfulAllOpenTrifIndicesInBox omega L N ↔ j ∈ box d N ∧ BgfdFaithfulAllOpenTrifAt omega L j := by
-- proof
  apply StatMech.FrontierA.mem_bgfdFaithfulAllOpenTrifIndicesInBox

/--
[bgfdFaithfulAllOpenTrifIndicesInBox_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenCoarseBoundaryGeneral.lean)
-/
@[path]
private lemma bgfdFaithfulAllOpenTrifIndicesInBox_count_eq
  {d : ℕ}
  {omega : ConfigSpace (Sym2 (Site d))}
  {L N : ℕ} :
-- imply
  (bgfdFaithfulAllOpenTrifIndicesInBox omega L N).card ≤ (vertexBoundary_finite d ((2 * L + 1) * N + L + 1)).toFinset.card := by
-- proof
  apply StatMech.FrontierA.bgfdFaithfulAllOpenTrifIndicesInBox_count omega L N


-- created on 2026-10-23
