import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc_raydisjoint
open Set StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Walls


/--
[bc_rayCell_distinct_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc_raydisjoint.lean)
-/
@[path]
private lemma bc_rayCell_distinct_of_ne_eq
  {d : ℕ}
  {i j : Fin d}
  {s t : ℤ}
-- given
  (h : i ≠ j)
  (hs : s ≠ 0) :
-- imply
  (hrHD_rayPt i s : Site d) ≠ hrHD_rayPt j t := by
-- proof
  apply StatMech.Walls.bc_rayCell_distinct_of_ne h hs

/--
[bc_rayCell_eq_iff_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc_raydisjoint.lean)
-/
@[path]
private lemma bc_rayCell_eq_iff_origin_eq
  {d : ℕ}
  {i j : Fin d}
  {s t : ℤ}
-- given
  (h : i ≠ j) :
-- imply
  (hrHD_rayPt i s : Site d) = hrHD_rayPt j t ↔ (s = 0 ∧ t = 0) := by
-- proof
  apply StatMech.Walls.bc_rayCell_eq_iff_origin h s t

/--
[bc_corridorRay_inter_eq_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc_raydisjoint.lean)
-/
@[path]
private lemma bc_corridorRay_inter_eq_origin_eq
  {d : ℕ}
  {i j : Fin d}
-- given
  (h : i ≠ j) :
-- imply
  corridorRay i ∩ corridorRay j = {(0 : Site d)} := by
-- proof
  apply StatMech.Walls.bc_corridorRay_inter_eq_origin h

/--
[bc_corridors_share_only_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc_raydisjoint.lean)
-/
@[path]
private lemma bc_corridors_share_only_origin_eq
  {d : ℕ}
  {i j : Fin d}
  {x : Site d}
-- given
  (h : i ≠ j)
  (hx : x ≠ 0) :
-- imply
  ¬ (x ∈ corridorRay i ∧ x ∈ corridorRay j) := by
-- proof
  apply StatMech.Walls.bc_corridors_share_only_origin h hx

/--
[bc_ray_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc_raydisjoint.lean)
-/
@[path]
private lemma bc_ray_disjoint_eq
  {d : ℕ} :
-- imply
  ∀ {i j : Fin d}, i ≠ j → (∀ s t : ℤ, s ≠ 0 → (hrHD_rayPt i s : Site d) ≠ hrHD_rayPt j t) ∧ corridorRay i ∩ corridorRay j = {(0 : Site d)} := by
-- proof
  apply StatMech.Walls.bc_ray_disjoint

/--
[bc_unit_cell_mem_corridor_ne_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc_raydisjoint.lean)
-/
@[path]
private lemma bc_unit_cell_mem_corridor_ne_origin_eq
  {d : ℕ}
  {j : Fin d} :
-- imply
  (hrHD_rayPt j 1 : Site d) ∈ corridorRay j ∧ (hrHD_rayPt j 1 : Site d) ≠ 0 := by
-- proof
  apply StatMech.Walls.bc_unit_cell_mem_corridor_ne_origin j

/--
[bc_ray_disjoint_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc_raydisjoint.lean)
-/
@[path]
private lemma bc_ray_disjoint_nonvacuous_eq
  {d : ℕ}
-- given
  (hd : 2 ≤ d) :
-- imply
  ∃ i j : Fin d, i ≠ j ∧ (hrHD_rayPt i 1 : Site d) ≠ 0 ∧ (hrHD_rayPt j 1 : Site d) ≠ 0 ∧ (hrHD_rayPt i 1 : Site d) ≠ hrHD_rayPt j 1 ∧ corridorRay i ∩ corridorRay j = {(0 : Site d)} := by
-- proof
  apply StatMech.Walls.bc_ray_disjoint_nonvacuous hd


-- created on 2026-10-23
