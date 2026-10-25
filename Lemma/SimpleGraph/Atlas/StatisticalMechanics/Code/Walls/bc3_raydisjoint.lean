import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc3_raydisjoint
open Set SimpleGraph SimpleGraph.Walk StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Walls


/--
[bc3_corridorWalk_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_raydisjoint.lean)
-/
@[path]
private lemma bc3_corridorWalk_succ_eq
  {d : ℕ}
  {j : Fin d}
  {p : ℕ} :
-- imply
  bc3_corridorWalk j (p + 1) = (bc3_corridorWalk j p).concat (by have h := hrHD_adj_rayPt j (p : ℤ) have he : ((p : ℤ) + 1) = ((p + 1 : ℕ) : ℤ) := by push_cast; ring rw [he] at h; exact h) := by
-- proof
  apply StatMech.Walls.bc3_corridorWalk_succ j p

/--
[bc3_corridorWalk_support_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_raydisjoint.lean)
-/
@[path]
private lemma bc3_corridorWalk_support_zero_eq
  {d : ℕ}
  {j : Fin d} :
-- imply
  (bc3_corridorWalk j 0).support = [hrHD_rayPt j 0] := by
-- proof
  apply StatMech.Walls.bc3_corridorWalk_support_zero j

/--
[bc3_corridorWalk_mem_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_raydisjoint.lean)
-/
@[path]
private lemma bc3_corridorWalk_mem_support_eq
  {d : ℕ}
  {j : Fin d}
  {L : ℕ}
  {x : Site d} :
-- imply
  x ∈ (bc3_corridorWalk j L).support ↔ ∃ t : ℕ, t ≤ L ∧ x = hrHD_rayPt j (t : ℤ) := by
-- proof
  apply StatMech.Walls.bc3_corridorWalk_mem_support j L x

/--
[bc3_corridorWalk_support_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_raydisjoint.lean)
-/
@[path]
private lemma bc3_corridorWalk_support_subset_eq
  {d : ℕ}
  {j : Fin d}
  {L : ℕ} :
-- imply
  ∀ x ∈ (bc3_corridorWalk j L).support, x ∈ corridorRay j := by
-- proof
  apply StatMech.Walls.bc3_corridorWalk_support_subset j L

/--
[bc3_origin_mem_corridorWalk_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_raydisjoint.lean)
-/
@[path]
private lemma bc3_origin_mem_corridorWalk_support_eq
  {d : ℕ}
  {j : Fin d}
  {L : ℕ} :
-- imply
  (0 : Site d) ∈ (bc3_corridorWalk j L).support := by
-- proof
  apply StatMech.Walls.bc3_origin_mem_corridorWalk_support j L

/--
[bc3_rayPt_inj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_raydisjoint.lean)
-/
@[path]
private lemma bc3_rayPt_inj_eq
  {d : ℕ}
  {j : Fin d}
  {s t : ℤ}
-- given
  (h : hrHD_rayPt j s = hrHD_rayPt j t) :
-- imply
  s = t := by
-- proof
  apply StatMech.Walls.bc3_rayPt_inj j h

/--
[bc3_corridorWalk_isPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_raydisjoint.lean)
-/
@[path]
private lemma bc3_corridorWalk_isPath_eq
  {d : ℕ}
  {j : Fin d}
  {L : ℕ} :
-- imply
  (bc3_corridorWalk j L).IsPath := by
-- proof
  apply StatMech.Walls.bc3_corridorWalk_isPath j L

/--
[bc3_corridorEdges_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_raydisjoint.lean)
-/
@[path]
private lemma bc3_corridorEdges_mono_eq
  {d : ℕ}
  {j : Fin d}
  {L L' : ℕ}
-- given
  (h : L ≤ L') :
-- imply
  hrHD_corridorEdges j L ⊆ hrHD_corridorEdges j L' := by
-- proof
  apply StatMech.Walls.bc3_corridorEdges_mono j h

/--
[bc3_corridorWalk_edges_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_raydisjoint.lean)
-/
@[path]
private lemma bc3_corridorWalk_edges_mem_eq
  {d : ℕ}
  {j : Fin d}
  {L : ℕ} :
-- imply
  ∀ e ∈ (bc3_corridorWalk j L).edges, e ∈ hrHD_corridorEdges j L := by
-- proof
  apply StatMech.Walls.bc3_corridorWalk_edges_mem j L

/--
[bc3_corridorWalk_cross_eq_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_raydisjoint.lean)
-/
@[path]
private lemma bc3_corridorWalk_cross_eq_origin_eq
  {d : ℕ}
  {i j : Fin d}
  {L L' : ℕ}
  {x : Site d}
-- given
  (h : i ≠ j)
  (hxi : x ∈ (bc3_corridorWalk i L).support)
  (hxj : x ∈ (bc3_corridorWalk j L').support) :
-- imply
  x = 0 := by
-- proof
  apply StatMech.Walls.bc3_corridorWalk_cross_eq_origin h L L' hxi hxj

/--
[bc3_corridorWalk_disjoint_off_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_raydisjoint.lean)
-/
@[path]
private lemma bc3_corridorWalk_disjoint_off_origin_eq
  {d : ℕ}
  {i j : Fin d}
  {L L' : ℕ}
  {x : Site d}
-- given
  (h : i ≠ j)
  (hx0 : x ≠ 0)
  (hxi : x ∈ (bc3_corridorWalk i L).support)
  (hxj : x ∈ (bc3_corridorWalk j L').support) :
-- imply
  False := by
-- proof
  apply StatMech.Walls.bc3_corridorWalk_disjoint_off_origin h L L' hx0 hxi hxj

/--
[bc3_corridorFamily_disjoint_off_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_raydisjoint.lean)
-/
@[path]
private lemma bc3_corridorFamily_disjoint_off_origin_eq
  {d : ℕ}
  {ax : ι → Fin d}
  {len : ι → ℕ}
  {i i' : ι}
  {x : Site d}
-- given
  (hax : Function.Injective ax)
  (hii : i ≠ i')
  (hx0 : x ≠ 0)
  (hxi : x ∈ (bc3_corridorWalk (ax i) (len i)).support)
  (hxi' : x ∈ (bc3_corridorWalk (ax i') (len i')).support) :
-- imply
  False := by
-- proof
  apply StatMech.Walls.bc3_corridorFamily_disjoint_off_origin ax len hax hii hx0 hxi hxi'

/--
[bc3_ray_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_raydisjoint.lean)
-/
@[path]
private lemma bc3_ray_disjoint_eq
  {d : ℕ} :
-- imply
  ∀ {i j : Fin d}, i ≠ j → ∀ L L' : ℕ, (∀ s t : ℤ, s ≠ 0 → (hrHD_rayPt i s : Site d) ≠ hrHD_rayPt j t) ∧ (bc3_corridorWalk i L).IsPath ∧ (∀ x : Site d, x ∈ (bc3_corridorWalk i L).support → x ∈ (bc3_corridorWalk j L').support → x = 0) := by
-- proof
  apply StatMech.Walls.bc3_ray_disjoint

/--
[bc3_unit_mem_corridorWalk_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_raydisjoint.lean)
-/
@[path]
private lemma bc3_unit_mem_corridorWalk_support_eq
  {d : ℕ}
  {j : Fin d}
  {L : ℕ}
-- given
  (hL : 1 ≤ L) :
-- imply
  (hrHD_rayPt j 1 : Site d) ∈ (bc3_corridorWalk j L).support ∧ (hrHD_rayPt j 1 : Site d) ≠ 0 := by
-- proof
  apply StatMech.Walls.bc3_unit_mem_corridorWalk_support j hL

/--
[bc3_ray_disjoint_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_raydisjoint.lean)
-/
@[path]
private lemma bc3_ray_disjoint_nonvacuous_eq
  {d : ℕ}
-- given
  (hd : 2 ≤ d) :
-- imply
  ∃ i j : Fin d, i ≠ j ∧ (bc3_corridorWalk i 1).IsPath ∧ (bc3_corridorWalk j 1).IsPath ∧ (hrHD_rayPt i 1 : Site d) ≠ 0 ∧ (hrHD_rayPt j 1 : Site d) ≠ 0 ∧ (hrHD_rayPt i 1 : Site d) ∈ (bc3_corridorWalk i 1).support ∧ (hrHD_rayPt j 1 : Site d) ∈ (bc3_corridorWalk j 1).support ∧ (∀ x : Site d, x ∈ (bc3_corridorWalk i 1).support → x ∈ (bc3_corridorWalk j 1).support → x = 0) := by
-- proof
  apply StatMech.Walls.bc3_ray_disjoint_nonvacuous hd


-- created on 2026-10-23
