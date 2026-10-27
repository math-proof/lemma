import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Lattice.ExteriorDodgeClose
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[edc_mem_support_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExteriorDodgeClose.lean)
-/
@[path]
private lemma edc_mem_support_iff_eq
  {w : Site 2} :
-- imply
  w ∈ edc_Vc.support ↔ w ∈ edc_ring.support := by
-- proof
  apply StatMech.Lattice.edc_mem_support_iff w

/--
[edc_z_offSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExteriorDodgeClose.lean)
-/
@[path]
private lemma edc_z_offSupport_eq :
-- imply
  (![(0:ℤ),0] : Site 2) ∉ edc_Vc.support := by
-- proof
  apply StatMech.Lattice.edc_z_offSupport

/--
[edc_neighbours_onSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExteriorDodgeClose.lean)
-/
@[path]
private lemma edc_neighbours_onSupport_eq :
-- imply
  (![(1:ℤ),0] : Site 2) ∈ edc_Vc.support ∧ (![(-1:ℤ),0] : Site 2) ∈ edc_Vc.support ∧ (![(0:ℤ),1] : Site 2) ∈ edc_Vc.support ∧ (![(0:ℤ),-1] : Site 2) ∈ edc_Vc.support := by
-- proof
  apply StatMech.Lattice.edc_neighbours_onSupport

/--
[edc_adj_centre_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExteriorDodgeClose.lean)
-/
@[path]
private lemma edc_adj_centre_cases_eq
  {y : Site 2}
-- given
  (h : (hypercubicLattice 2).Adj (![(0:ℤ),0] : Site 2) y) :
-- imply
  y = ![1,0] ∨ y = ![-1,0] ∨ y = ![0,1] ∨ y = ![0,-1] := by
-- proof
  apply StatMech.Lattice.edc_adj_centre_cases h

/--
[edc_z_isolated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExteriorDodgeClose.lean)
-/
@[path]
private lemma edc_z_isolated_eq
  {y : Site 2} :
-- imply
  ¬ (offSupport edc_Vc).Adj (![(0:ℤ),0] : Site 2) y := by
-- proof
  apply StatMech.Lattice.edc_z_isolated y

/--
[edc_isolated_walk_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExteriorDodgeClose.lean)
-/
@[path]
private lemma edc_isolated_walk_eq_eq
  {w : Site 2}
  {p : (offSupport edc_Vc).Walk (![(0:ℤ),0] : Site 2) w} :
-- imply
  w = ![0,0] := by
-- proof
  apply StatMech.Lattice.edc_isolated_walk_eq p

/--
[edc_isolated_reachable_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExteriorDodgeClose.lean)
-/
@[path]
private lemma edc_isolated_reachable_eq_eq
  {w : Site 2}
-- given
  (h : (offSupport edc_Vc).Reachable (![(0:ℤ),0] : Site 2) w) :
-- imply
  w = ![0,0] := by
-- proof
  apply StatMech.Lattice.edc_isolated_reachable_eq h

/--
[edc_rayCount_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExteriorDodgeClose.lean)
-/
@[path]
private lemma edc_rayCount_even_eq
  {z : Site 2} :
-- imply
  Even (jec_rayCount z edc_Vc) := by
-- proof
  apply StatMech.Lattice.edc_rayCount_even z

/--
[edc_z_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExteriorDodgeClose.lean)
-/
@[path]
private lemma edc_z_outside_eq :
-- imply
  (![(0:ℤ),0] : Site 2) ∉ jec_leftRegion edc_Vc := by
-- proof
  apply StatMech.Lattice.edc_z_outside

/--
[edc_rightStep_refuted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExteriorDodgeClose.lean)
-/
@[path]
private lemma edc_rightStep_refuted_eq
  {R : ℕ} :
-- imply
  ¬ ecc_RightStep edc_Vc R := by
-- proof
  apply StatMech.Lattice.edc_rightStep_refuted R

/--
[edc_rightDodge_refuted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExteriorDodgeClose.lean)
-/
@[path]
private lemma edc_rightDodge_refuted_eq
  {R : ℕ} :
-- imply
  ¬ ecc_RightDodge edc_Vc R := by
-- proof
  apply StatMech.Lattice.edc_rightDodge_refuted R

/--
[edc_centre_reaches_only_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExteriorDodgeClose.lean)
-/
@[path]
private lemma edc_centre_reaches_only_self_eq
  {w : Site 2}
-- given
  (h : (offSupport edc_Vc).Reachable (![(0:ℤ),0] : Site 2) w) :
-- imply
  w 0 = 0 ∧ w 1 = 0 := by
-- proof
  apply StatMech.Lattice.edc_centre_reaches_only_self h


-- created on 2026-10-23
