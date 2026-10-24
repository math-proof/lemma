import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.kc3_tailinK
open Set SimpleGraph Function StatMech StatMech.Walls


/--
[kc3_iterate_isBoundaryDart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_tailinK.lean)
-/
@[path]
private lemma kc3_iterate_isBoundaryDart_eq
  {K : Set (Site 2)}
  {e : Dart}
  {k : ℕ}
-- given
  (he : IsBoundaryDart K e) :
-- imply
  IsBoundaryDart K ((dartNext K)^[k] e) := by
-- proof
  apply StatMech.Walls.kc3_iterate_isBoundaryDart K e he k

/--
[kc3_iterate_tail_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_tailinK.lean)
-/
@[path]
private lemma kc3_iterate_tail_mem_eq
  {K : Set (Site 2)}
  {e : Dart}
  {k : ℕ}
-- given
  (he : IsBoundaryDart K e) :
-- imply
  ((dartNext K)^[k] e).tail ∈ K := by
-- proof
  apply StatMech.Walls.kc3_iterate_tail_mem K e he k

/--
[kc3_iterate_head_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_tailinK.lean)
-/
@[path]
private lemma kc3_iterate_head_not_mem_eq
  {K : Set (Site 2)}
  {e : Dart}
  {k : ℕ}
-- given
  (he : IsBoundaryDart K e) :
-- imply
  ((dartNext K)^[k] e).head ∉ K := by
-- proof
  apply StatMech.Walls.kc3_iterate_head_not_mem K e he k

/--
[kc3_orbitSub_iterate_tail_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_tailinK.lean)
-/
@[path]
private lemma kc3_orbitSub_iterate_tail_mem_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {k : ℕ} :
-- imply
  ((dartNextSub K)^[k] a).1.tail ∈ K := by
-- proof
  apply StatMech.Walls.kc3_orbitSub_iterate_tail_mem K a k

/--
[kc3_orbit_support_tail_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_tailinK.lean)
-/
@[path]
private lemma kc3_orbit_support_tail_mem_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {d : {e : Dart // IsBoundaryDart K e}}
-- given
  (_hd : d ∈ (dartOrbitWalk K a).support) :
-- imply
  d.1.tail ∈ K := by
-- proof
  apply StatMech.Walls.kc3_orbit_support_tail_mem K a _hd

/--
[kc3_tail_isCellCorner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_tailinK.lean)
-/
@[path]
private lemma kc3_tail_isCellCorner_eq
  {e : Dart} :
-- imply
  kc3_IsCellCorner (dartFace e) e.tail := by
-- proof
  apply StatMech.Walls.kc3_tail_isCellCorner e

/--
[kc3_cellCorner_coord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_tailinK.lean)
-/
@[path]
private lemma kc3_cellCorner_coord_eq
  {f q : Site 2}
-- given
  (h : kc3_IsCellCorner f q) :
-- imply
  (q 0 = f 0 ∨ q 0 = f 0 + 1) ∧ (q 1 = f 1 ∨ q 1 = f 1 + 1) := by
-- proof
  apply StatMech.Walls.kc3_cellCorner_coord h

/--
[kc3_faceCorner_in_K](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_tailinK.lean)
-/
@[path]
private lemma kc3_faceCorner_in_K_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (he : IsBoundaryDart K e) :
-- imply
  kc3_IsCellCorner (dartFace e) e.tail ∧ e.tail ∈ K := by
-- proof
  apply StatMech.Walls.kc3_faceCorner_in_K he

/--
[kc3_iterate_faceCorner_in_K](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_tailinK.lean)
-/
@[path]
private lemma kc3_iterate_faceCorner_in_K_eq
  {K : Set (Site 2)}
  {e : Dart}
  {k : ℕ}
-- given
  (he : IsBoundaryDart K e) :
-- imply
  kc3_IsCellCorner (dartFace ((dartNext K)^[k] e)) ((dartNext K)^[k] e).tail ∧ ((dartNext K)^[k] e).tail ∈ K := by
-- proof
  apply StatMech.Walls.kc3_iterate_faceCorner_in_K K e he k

/--
[kc3_left_face_SW](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_tailinK.lean)
-/
@[path]
private lemma kc3_left_face_SW_eq
  {e : Dart}
-- given
  (hd : e.dir = ![-1, 0]) :
-- imply
  dartFace e = ![e.tail 0 - 1, e.tail 1 - 1] := by
-- proof
  apply StatMech.Walls.kc3_left_face_SW e hd

/--
[kc3_left_tail_eq_NE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_tailinK.lean)
-/
@[path]
private lemma kc3_left_tail_eq_NE_eq
  {e : Dart}
-- given
  (hd : e.dir = ![-1, 0]) :
-- imply
  e.tail = npd_P11 (dartFace e) := by
-- proof
  apply StatMech.Walls.kc3_left_tail_eq_NE e hd

/--
[kc3_left_extremeCell_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_tailinK.lean)
-/
@[path]
private lemma kc3_left_extremeCell_mem_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (he : IsBoundaryDart K e)
  (hd : e.dir = ![-1, 0]) :
-- imply
  npd_P11 (dartFace e) ∈ K := by
-- proof
  apply StatMech.Walls.kc3_left_extremeCell_mem he hd

/--
[kc3_left_extremeCell_mem_coord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_tailinK.lean)
-/
@[path]
private lemma kc3_left_extremeCell_mem_coord_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (he : IsBoundaryDart K e)
  (hd : e.dir = ![-1, 0]) :
-- imply
  (![dartFace e 0 + 1, dartFace e 1 + 1] : Site 2) ∈ K := by
-- proof
  apply StatMech.Walls.kc3_left_extremeCell_mem_coord he hd

/--
[kc3_left_face_ne_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_tailinK.lean)
-/
@[path]
private lemma kc3_left_face_ne_tail_eq
  {e : Dart}
-- given
  (hd : e.dir = ![-1, 0]) :
-- imply
  dartFace e ≠ e.tail := by
-- proof
  apply StatMech.Walls.kc3_left_face_ne_tail e hd

/--
[kc3_tailInK_node](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_tailinK.lean)
-/
@[path]
private lemma kc3_tailInK_node_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (he : IsBoundaryDart K e) :
-- imply
  e.tail ∈ K ∧ kc3_IsCellCorner (dartFace e) e.tail ∧ (e.dir = ![-1, 0] → dartFace e = ![e.tail 0 - 1, e.tail 1 - 1] ∧ e.tail = npd_P11 (dartFace e) ∧ npd_P11 (dartFace e) ∈ K) := by
-- proof
  apply StatMech.Walls.kc3_tailInK_node he

/--
[kc3_iterate_tailInK_node](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_tailinK.lean)
-/
@[path]
private lemma kc3_iterate_tailInK_node_eq
  {K : Set (Site 2)}
  {e : Dart}
  {k : ℕ}
-- given
  (he : IsBoundaryDart K e) :
-- imply
  ((dartNext K)^[k] e).tail ∈ K ∧ kc3_IsCellCorner (dartFace ((dartNext K)^[k] e)) ((dartNext K)^[k] e).tail ∧ (((dartNext K)^[k] e).dir = ![-1, 0] → dartFace ((dartNext K)^[k] e) = ![((dartNext K)^[k] e).tail 0 - 1, ((dartNext K)^[k] e).tail 1 - 1] ∧ ((dartNext K)^[k] e).tail = npd_P11 (dartFace ((dartNext K)^[k] e)) ∧ npd_P11 (dartFace ((dartNext K)^[k] e)) ∈ K) := by
-- proof
  apply StatMech.Walls.kc3_iterate_tailInK_node K e he k

/--
[kc3_witLeftDart_dir](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_tailinK.lean)
-/
@[path]
private lemma kc3_witLeftDart_dir_eq :
-- imply
  kc3_witLeftDart.dir = ![-1, 0] := by
-- proof
  apply StatMech.Walls.kc3_witLeftDart_dir

/--
[kc3_witLeftDart_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_tailinK.lean)
-/
@[path]
private lemma kc3_witLeftDart_tail_eq :
-- imply
  kc3_witLeftDart.tail = ![1, 1] := by
-- proof
  apply StatMech.Walls.kc3_witLeftDart_tail

/--
[kc3_witLeftDart_face](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_tailinK.lean)
-/
@[path]
private lemma kc3_witLeftDart_face_eq :
-- imply
  dartFace kc3_witLeftDart = ![0, 0] := by
-- proof
  apply StatMech.Walls.kc3_witLeftDart_face

/--
[kc3_witLeftDart_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_tailinK.lean)
-/
@[path]
private lemma kc3_witLeftDart_head_eq :
-- imply
  kc3_witLeftDart.head = ![0, 1] := by
-- proof
  apply StatMech.Walls.kc3_witLeftDart_head

/--
[kc3_witLeftDart_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_tailinK.lean)
-/
@[path]
private lemma kc3_witLeftDart_boundary_eq :
-- imply
  IsBoundaryDart ({![1, 1]} : Set (Site 2)) kc3_witLeftDart := by
-- proof
  apply StatMech.Walls.kc3_witLeftDart_boundary

/--
[kc3_node_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_tailinK.lean)
-/
@[path]
private lemma kc3_node_nonvacuous_eq :
-- imply
  kc3_witLeftDart.tail ∈ ({![1, 1]} : Set (Site 2)) ∧ kc3_IsCellCorner (dartFace kc3_witLeftDart) kc3_witLeftDart.tail ∧ (kc3_witLeftDart.dir = ![-1, 0] → dartFace kc3_witLeftDart = ![kc3_witLeftDart.tail 0 - 1, kc3_witLeftDart.tail 1 - 1] ∧ kc3_witLeftDart.tail = npd_P11 (dartFace kc3_witLeftDart) ∧ npd_P11 (dartFace kc3_witLeftDart) ∈ ({![1, 1]} : Set (Site 2))) := by
-- proof
  apply StatMech.Walls.kc3_node_nonvacuous


-- created on 2026-10-23
