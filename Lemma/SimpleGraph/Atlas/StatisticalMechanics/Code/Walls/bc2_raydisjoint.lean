import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bc2_raydisjoint
open Set StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Walls


/--
[bc2_rayCell_distinct_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_raydisjoint.lean)
-/
@[path]
private lemma bc2_rayCell_distinct_of_ne_eq
  {d : ℕ}
  {i j : Fin d}
  {s t : ℤ}
-- given
  (h : i ≠ j)
  (hs : s ≠ 0) :
-- imply
  (hrHD_rayPt i s : Site d) ≠ hrHD_rayPt j t := by
-- proof
  apply StatMech.Walls.bc2_rayCell_distinct_of_ne h hs

/--
[bc2_rayCell_distinct_of_ne'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_raydisjoint.lean)
-/
@[path]
private lemma bc2_rayCell_distinct_of_ne'_eq
  {d : ℕ}
  {i j : Fin d}
  {s t : ℤ}
-- given
  (h : i ≠ j)
  (ht : t ≠ 0) :
-- imply
  (hrHD_rayPt i s : Site d) ≠ hrHD_rayPt j t := by
-- proof
  apply StatMech.Walls.bc2_rayCell_distinct_of_ne' h ht

/--
[bc2_rayCell_eq_iff_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_raydisjoint.lean)
-/
@[path]
private lemma bc2_rayCell_eq_iff_origin_eq
  {d : ℕ}
  {i j : Fin d}
  {s t : ℤ}
-- given
  (h : i ≠ j) :
-- imply
  (hrHD_rayPt i s : Site d) = hrHD_rayPt j t ↔ (s = 0 ∧ t = 0) := by
-- proof
  apply StatMech.Walls.bc2_rayCell_eq_iff_origin h s t

/--
[bc2_corridorVerts_subset_corridorRay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_raydisjoint.lean)
-/
@[path]
private lemma bc2_corridorVerts_subset_corridorRay_eq
  {d : ℕ}
  {j : Fin d}
  {L : ℕ} :
-- imply
  bc2_corridorVerts j L ⊆ corridorRay j := by
-- proof
  apply StatMech.Walls.bc2_corridorVerts_subset_corridorRay j L

/--
[bc2_corridorVerts_inter_subset_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_raydisjoint.lean)
-/
@[path]
private lemma bc2_corridorVerts_inter_subset_origin_eq
  {d : ℕ}
  {i j : Fin d}
  {L L' : ℕ}
-- given
  (h : i ≠ j) :
-- imply
  bc2_corridorVerts i L ∩ bc2_corridorVerts j L' ⊆ {(0 : Site d)} := by
-- proof
  apply StatMech.Walls.bc2_corridorVerts_inter_subset_origin h L L'

/--
[bc2_origin_mem_corridorVerts_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_raydisjoint.lean)
-/
@[path]
private lemma bc2_origin_mem_corridorVerts_iff_eq
  {d : ℕ}
  {j : Fin d}
  {L : ℕ} :
-- imply
  (0 : Site d) ∈ bc2_corridorVerts j L ↔ 0 < L := by
-- proof
  apply StatMech.Walls.bc2_origin_mem_corridorVerts_iff j L

/--
[bc2_corridorEdges_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_raydisjoint.lean)
-/
@[path]
private lemma bc2_corridorEdges_disjoint_eq
  {d : ℕ}
  {i j : Fin d}
  {L L' : ℕ}
-- given
  (h : i ≠ j) :
-- imply
  Disjoint (hrHD_corridorEdges i L) (hrHD_corridorEdges j L') := by
-- proof
  apply StatMech.Walls.bc2_corridorEdges_disjoint h L L'

/--
[bc2_ray_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_raydisjoint.lean)
-/
@[path]
private lemma bc2_ray_disjoint_eq
  {d : ℕ} :
-- imply
  ∀ {i j : Fin d}, i ≠ j → ∀ L L' : ℕ, (∀ s t : ℤ, s ≠ 0 → (hrHD_rayPt i s : Site d) ≠ hrHD_rayPt j t) ∧ Disjoint (hrHD_corridorEdges i L) (hrHD_corridorEdges j L') ∧ bc2_corridorVerts i L ∩ bc2_corridorVerts j L' ⊆ {(0 : Site d)} := by
-- proof
  apply StatMech.Walls.bc2_ray_disjoint

/--
[bc2_forced_corridors_share_only_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_raydisjoint.lean)
-/
@[path]
private lemma bc2_forced_corridors_share_only_origin_eq
  {d : ℕ}
  {i j : Fin d}
  {L L' : ℕ}
-- given
  (h : i ≠ j) :
-- imply
  Disjoint (hrHD_corridorEdges i L) (hrHD_corridorEdges j L') ∧ (∀ x : Site d, x ≠ 0 → ¬ (x ∈ bc2_corridorVerts i L ∧ x ∈ bc2_corridorVerts j L')) := by
-- proof
  apply StatMech.Walls.bc2_forced_corridors_share_only_origin h L L'

/--
[bc2_unit_cell_mem_corridorVerts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_raydisjoint.lean)
-/
@[path]
private lemma bc2_unit_cell_mem_corridorVerts_eq
  {d : ℕ}
  {j : Fin d}
  {L : ℕ}
-- given
  (hL : 0 < L) :
-- imply
  (hrHD_rayPt j 1 : Site d) ∈ bc2_corridorVerts j L ∧ (hrHD_rayPt j 1 : Site d) ≠ 0 := by
-- proof
  apply StatMech.Walls.bc2_unit_cell_mem_corridorVerts j hL

/--
[bc2_ray_disjoint_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_raydisjoint.lean)
-/
@[path]
private lemma bc2_ray_disjoint_nonvacuous_eq
  {d : ℕ}
-- given
  (hd : 2 ≤ d) :
-- imply
  ∃ i j : Fin d, i ≠ j ∧ (hrHD_rayPt i 1 : Site d) ≠ 0 ∧ (hrHD_rayPt j 1 : Site d) ≠ 0 ∧ (hrHD_rayPt i 1 : Site d) ≠ hrHD_rayPt j 1 ∧ Disjoint (hrHD_corridorEdges i 1) (hrHD_corridorEdges j 1) ∧ bc2_corridorVerts i 1 ∩ bc2_corridorVerts j 1 ⊆ {(0 : Site d)} := by
-- proof
  apply StatMech.Walls.bc2_ray_disjoint_nonvacuous hd


-- created on 2026-10-23
