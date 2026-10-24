import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.StraightWalk
open Set SimpleGraph StatMech StatMech.Lattice


/--
[sw_adj_horizSucc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StraightWalk.lean)
-/
@[path]
private lemma sw_adj_horizSucc_eq
  {y x : ℤ} :
-- imply
  (hypercubicLattice 2).Adj ![x, y] ![x + 1, y] := by
-- proof
  apply StatMech.Lattice.sw_adj_horizSucc y x

/--
[sw_adj_vertSucc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StraightWalk.lean)
-/
@[path]
private lemma sw_adj_vertSucc_eq
  {x y : ℤ} :
-- imply
  (hypercubicLattice 2).Adj ![x, y] ![x, y + 1] := by
-- proof
  apply StatMech.Lattice.sw_adj_vertSucc x y

/--
[sw_horizR_support_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StraightWalk.lean)
-/
@[path]
private lemma sw_horizR_support_eq_eq
  {y x0 : ℤ}
  {m : ℕ} :
-- imply
  (sw_horizR y x0 (m + 1)).support = (sw_horizR y x0 m).support ++ [![x0 + (m : ℤ) + 1, y]] := by
-- proof
  apply StatMech.Lattice.sw_horizR_support_eq y x0 m

/--
[sw_vertU_support_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StraightWalk.lean)
-/
@[path]
private lemma sw_vertU_support_eq_eq
  {x y0 : ℤ}
  {m : ℕ} :
-- imply
  (sw_vertU x y0 (m + 1)).support = (sw_vertU x y0 m).support ++ [![x, y0 + (m : ℤ) + 1]] := by
-- proof
  apply StatMech.Lattice.sw_vertU_support_eq x y0 m

/--
[sw_horizR_mem_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StraightWalk.lean)
-/
@[path]
private lemma sw_horizR_mem_support_eq
  {y x0 : ℤ}
  {n : ℕ}
  {z : Site 2} :
-- imply
  z ∈ (sw_horizR y x0 n).support ↔ ∃ t : ℤ, 0 ≤ t ∧ t ≤ (n : ℤ) ∧ z = ![x0 + t, y] := by
-- proof
  apply StatMech.Lattice.sw_horizR_mem_support y x0 n z

/--
[sw_vertU_mem_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StraightWalk.lean)
-/
@[path]
private lemma sw_vertU_mem_support_eq
  {x y0 : ℤ}
  {n : ℕ}
  {z : Site 2} :
-- imply
  z ∈ (sw_vertU x y0 n).support ↔ ∃ t : ℤ, 0 ≤ t ∧ t ≤ (n : ℤ) ∧ z = ![x, y0 + t] := by
-- proof
  apply StatMech.Lattice.sw_vertU_mem_support x y0 n z

/--
[sw_horizR_support_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StraightWalk.lean)
-/
@[path]
private lemma sw_horizR_support_nodup_eq
  {y x0 : ℤ}
  {n : ℕ} :
-- imply
  (sw_horizR y x0 n).support.Nodup := by
-- proof
  apply StatMech.Lattice.sw_horizR_support_nodup y x0 n

/--
[sw_vertU_support_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StraightWalk.lean)
-/
@[path]
private lemma sw_vertU_support_nodup_eq
  {x y0 : ℤ}
  {n : ℕ} :
-- imply
  (sw_vertU x y0 n).support.Nodup := by
-- proof
  apply StatMech.Lattice.sw_vertU_support_nodup x y0 n

/--
[sw_horizSeg_mem_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StraightWalk.lean)
-/
@[path]
private lemma sw_horizSeg_mem_support_eq
  {y x0 x1 : ℤ}
  {z : Site 2} :
-- imply
  z ∈ (sw_horizSeg y x0 x1).support ↔ ∃ t : ℤ, t ∈ Set.uIcc x0 x1 ∧ z = ![t, y] := by
-- proof
  apply StatMech.Lattice.sw_horizSeg_mem_support y x0 x1 z

/--
[sw_vertSeg_mem_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StraightWalk.lean)
-/
@[path]
private lemma sw_vertSeg_mem_support_eq
  {x y0 y1 : ℤ}
  {z : Site 2} :
-- imply
  z ∈ (sw_vertSeg x y0 y1).support ↔ ∃ t : ℤ, t ∈ Set.uIcc y0 y1 ∧ z = ![x, t] := by
-- proof
  apply StatMech.Lattice.sw_vertSeg_mem_support x y0 y1 z

/--
[sw_seg_support_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StraightWalk.lean)
-/
@[path]
private lemma sw_seg_support_mem_eq
  {y x0 x1 a b : ℤ} :
-- imply
  (![a, b] : Site 2) ∈ (sw_horizSeg y x0 x1).support ↔ b = y ∧ a ∈ Set.uIcc x0 x1 := by
-- proof
  apply StatMech.Lattice.sw_seg_support_mem y x0 x1 a b

/--
[sw_horizSeg_support_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StraightWalk.lean)
-/
@[path]
private lemma sw_horizSeg_support_subset_eq
  {y x0 x1 : ℤ} :
-- imply
  {z : Site 2 | z ∈ (sw_horizSeg y x0 x1).support} ⊆ (fun t => (![t, y] : Site 2)) '' Set.uIcc x0 x1 := by
-- proof
  apply StatMech.Lattice.sw_horizSeg_support_subset y x0 x1

/--
[sw_vertSeg_support_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StraightWalk.lean)
-/
@[path]
private lemma sw_vertSeg_support_subset_eq
  {x y0 y1 : ℤ} :
-- imply
  {z : Site 2 | z ∈ (sw_vertSeg x y0 y1).support} ⊆ (fun t => (![x, t] : Site 2)) '' Set.uIcc y0 y1 := by
-- proof
  apply StatMech.Lattice.sw_vertSeg_support_subset x y0 y1

/--
[sw_horizSeg_support_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StraightWalk.lean)
-/
@[path]
private lemma sw_horizSeg_support_nodup_eq
  {y x0 x1 : ℤ} :
-- imply
  (sw_horizSeg y x0 x1).support.Nodup := by
-- proof
  apply StatMech.Lattice.sw_horizSeg_support_nodup y x0 x1

/--
[sw_vertSeg_support_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StraightWalk.lean)
-/
@[path]
private lemma sw_vertSeg_support_nodup_eq
  {x y0 y1 : ℤ} :
-- imply
  (sw_vertSeg x y0 y1).support.Nodup := by
-- proof
  apply StatMech.Lattice.sw_vertSeg_support_nodup x y0 y1

/--
[sw_seg_nodup_of_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StraightWalk.lean)
-/
@[path]
private lemma sw_seg_nodup_of_distinct_eq
  {y x0 x1 : ℤ}
-- given
  (hne : x0 ≠ x1) :
-- imply
  (sw_horizSeg y x0 x1).support.Nodup ∧ (![x0, y] : Site 2) ≠ ![x1, y] := by
-- proof
  apply StatMech.Lattice.sw_seg_nodup_of_distinct y x0 x1 hne

/--
[sw_lshape_mem_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StraightWalk.lean)
-/
@[path]
private lemma sw_lshape_mem_support_eq
  {x0 y0 x1 y1 : ℤ}
  {z : Site 2} :
-- imply
  z ∈ (sw_lshape x0 y0 x1 y1).support ↔ z ∈ (sw_horizSeg y0 x0 x1).support ∨ z ∈ (sw_vertSeg x1 y0 y1).support := by
-- proof
  apply StatMech.Lattice.sw_lshape_mem_support x0 y0 x1 y1 z

/--
[sw_lshape_support_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StraightWalk.lean)
-/
@[path]
private lemma sw_lshape_support_eq_eq
  {x0 y0 x1 y1 : ℤ}
  {z : Site 2} :
-- imply
  z ∈ (sw_lshape x0 y0 x1 y1).support ↔ (∃ t : ℤ, t ∈ Set.uIcc x0 x1 ∧ z = ![t, y0]) ∨ (∃ t : ℤ, t ∈ Set.uIcc y0 y1 ∧ z = ![x1, t]) := by
-- proof
  apply StatMech.Lattice.sw_lshape_support_eq x0 y0 x1 y1 z


-- created on 2026-10-23
