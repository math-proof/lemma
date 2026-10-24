import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.InteriorWindingClose
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[iwc_mem_rightPocket](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InteriorWindingClose.lean)
-/
@[path]
private lemma iwc_mem_rightPocket_eq
  {z : Site 2} :
-- imply
  z ∈ iwc_RightPocket ↔ (z 0 = 5 ∨ z 0 = 6) ∧ (z 1 = 1 ∨ z 1 = 2 ∨ z 1 = 3) := by
-- proof
  apply StatMech.Lattice.iwc_mem_rightPocket z

/--
[iwc_on_42](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InteriorWindingClose.lean)
-/
@[path]
private lemma iwc_on_42_eq :
-- imply
  (![4, 2] : Site 2) ∈ sdc_fjord.support := by
-- proof
  apply StatMech.Lattice.iwc_on_42

/--
[iwc_on_43](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InteriorWindingClose.lean)
-/
@[path]
private lemma iwc_on_43_eq :
-- imply
  (![4, 3] : Site 2) ∈ sdc_fjord.support := by
-- proof
  apply StatMech.Lattice.iwc_on_43

/--
[iwc_on_72](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InteriorWindingClose.lean)
-/
@[path]
private lemma iwc_on_72_eq :
-- imply
  (![7, 2] : Site 2) ∈ sdc_fjord.support := by
-- proof
  apply StatMech.Lattice.iwc_on_72

/--
[iwc_on_73](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InteriorWindingClose.lean)
-/
@[path]
private lemma iwc_on_73_eq :
-- imply
  (![7, 3] : Site 2) ∈ sdc_fjord.support := by
-- proof
  apply StatMech.Lattice.iwc_on_73

/--
[iwc_on_54](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InteriorWindingClose.lean)
-/
@[path]
private lemma iwc_on_54_eq :
-- imply
  (![5, 4] : Site 2) ∈ sdc_fjord.support := by
-- proof
  apply StatMech.Lattice.iwc_on_54

/--
[iwc_on_64](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InteriorWindingClose.lean)
-/
@[path]
private lemma iwc_on_64_eq :
-- imply
  (![6, 4] : Site 2) ∈ sdc_fjord.support := by
-- proof
  apply StatMech.Lattice.iwc_on_64

/--
[iwc_rightPocket_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InteriorWindingClose.lean)
-/
@[path]
private lemma iwc_rightPocket_step_eq
  {u v : Site 2}
-- given
  (hu : u ∈ iwc_RightPocket)
  (hadj : (hypercubicLattice 2).Adj u v)
  (hv : v ∉ sdc_fjord.support) :
-- imply
  v ∈ iwc_RightPocket := by
-- proof
  apply StatMech.Lattice.iwc_rightPocket_step hu hadj hv

/--
[iwc_offSupport_walk_in_rightPocket](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InteriorWindingClose.lean)
-/
@[path]
private lemma iwc_offSupport_walk_in_rightPocket_eq
  {x y : Site 2}
  {p : (hypercubicLattice 2).Walk x y}
-- given
  (hp : ∀ w ∈ p.support, w ∉ sdc_fjord.support)
  (hx : x ∈ iwc_RightPocket) :
-- imply
  ∀ w ∈ p.support, w ∈ iwc_RightPocket := by
-- proof
  apply StatMech.Lattice.iwc_offSupport_walk_in_rightPocket p hp hx

/--
[iwc_mem_rightPocket_51](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InteriorWindingClose.lean)
-/
@[path]
private lemma iwc_mem_rightPocket_51_eq :
-- imply
  (![5, 1] : Site 2) ∈ iwc_RightPocket := by
-- proof
  apply StatMech.Lattice.iwc_mem_rightPocket_51

/--
[iwc_not_rightPocket_11](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InteriorWindingClose.lean)
-/
@[path]
private lemma iwc_not_rightPocket_11_eq :
-- imply
  (![1, 1] : Site 2) ∉ iwc_RightPocket := by
-- proof
  apply StatMech.Lattice.iwc_not_rightPocket_11

/--
[iwc_no_offSupport_walk_51_to_11](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InteriorWindingClose.lean)
-/
@[path]
private lemma iwc_no_offSupport_walk_51_to_11_eq :
-- imply
  ¬ ∃ p : (hypercubicLattice 2).Walk (![5, 1] : Site 2) (![1, 1] : Site 2), ∀ w ∈ p.support, w ∉ sdc_fjord.support := by
-- proof
  apply StatMech.Lattice.iwc_no_offSupport_walk_51_to_11

/--
[iwc_no_rowLinked_seed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InteriorWindingClose.lean)
-/
@[path]
private lemma iwc_no_rowLinked_seed_eq :
-- imply
  ¬ ∃ seed : Site 2, seed ∈ jil_offSupportInterior sdc_fjord ∧ jil_RowLinked sdc_fjord seed := by
-- proof
  apply StatMech.Lattice.iwc_no_rowLinked_seed

/--
[iwc_rowLinked_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InteriorWindingClose.lean)
-/
@[path]
private lemma iwc_rowLinked_false_eq :
-- imply
  ∃ seed : Site 2, seed ∈ jil_offSupportInterior sdc_fjord ∧ ¬ jil_RowLinked sdc_fjord seed := by
-- proof
  apply StatMech.Lattice.iwc_rowLinked_false

/--
[iwc_exists_rowLinked_seed_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InteriorWindingClose.lean)
-/
@[path]
private lemma iwc_exists_rowLinked_seed_false_eq :
-- imply
  ¬ ∃ seed ∈ jil_offSupportInterior sdc_fjord, jil_RowLinked sdc_fjord seed := by
-- proof
  apply StatMech.Lattice.iwc_exists_rowLinked_seed_false

/--
[iwc_interior_disconnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InteriorWindingClose.lean)
-/
@[path]
private lemma iwc_interior_disconnected_eq :
-- imply
  (![5, 1] : Site 2) ∈ jil_offSupportInterior sdc_fjord ∧ (![1, 1] : Site 2) ∈ jil_offSupportInterior sdc_fjord ∧ ¬ ∃ p : (hypercubicLattice 2).Walk (![5, 1] : Site 2) (![1, 1] : Site 2), ∀ w ∈ p.support, w ∉ sdc_fjord.support := by
-- proof
  apply StatMech.Lattice.iwc_interior_disconnected


-- created on 2026-10-23
