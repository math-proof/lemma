import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.kc2_tailinK
open Set SimpleGraph Function StatMech StatMech.Walls


/--
[kc2_iterate_isBoundaryDart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_tailinK.lean)
-/
@[path]
private lemma kc2_iterate_isBoundaryDart_eq
  {K : Set (Site 2)}
  {e : Dart}
  {k : ℕ}
-- given
  (he : IsBoundaryDart K e) :
-- imply
  IsBoundaryDart K ((dartNext K)^[k] e) := by
-- proof
  apply StatMech.Walls.kc2_iterate_isBoundaryDart K e he k

/--
[kc2_iterate_tail_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_tailinK.lean)
-/
@[path]
private lemma kc2_iterate_tail_mem_eq
  {K : Set (Site 2)}
  {e : Dart}
  {k : ℕ}
-- given
  (he : IsBoundaryDart K e) :
-- imply
  ((dartNext K)^[k] e).tail ∈ K := by
-- proof
  apply StatMech.Walls.kc2_iterate_tail_mem K e he k

/--
[kc2_iterate_head_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_tailinK.lean)
-/
@[path]
private lemma kc2_iterate_head_not_mem_eq
  {K : Set (Site 2)}
  {e : Dart}
  {k : ℕ}
-- given
  (he : IsBoundaryDart K e) :
-- imply
  ((dartNext K)^[k] e).head ∉ K := by
-- proof
  apply StatMech.Walls.kc2_iterate_head_not_mem K e he k

/--
[kc2_orbitSub_iterate_tail_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_tailinK.lean)
-/
@[path]
private lemma kc2_orbitSub_iterate_tail_mem_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {k : ℕ} :
-- imply
  ((dartNextSub K)^[k] a).1.tail ∈ K := by
-- proof
  apply StatMech.Walls.kc2_orbitSub_iterate_tail_mem K a k

/--
[kc2_orbit_support_tail_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_tailinK.lean)
-/
@[path]
private lemma kc2_orbit_support_tail_mem_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {d : {e : Dart // IsBoundaryDart K e}}
-- given
  (_hd : d ∈ (dartOrbitWalk K a).support) :
-- imply
  d.1.tail ∈ K := by
-- proof
  apply StatMech.Walls.kc2_orbit_support_tail_mem K a _hd

/--
[kc2_tail_isCellCorner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_tailinK.lean)
-/
@[path]
private lemma kc2_tail_isCellCorner_eq
  {e : Dart} :
-- imply
  kc2_IsCellCorner (dartFace e) e.tail := by
-- proof
  apply StatMech.Walls.kc2_tail_isCellCorner e

/--
[kc2_faceCorner_in_K](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_tailinK.lean)
-/
@[path]
private lemma kc2_faceCorner_in_K_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (he : IsBoundaryDart K e) :
-- imply
  kc2_IsCellCorner (dartFace e) e.tail ∧ e.tail ∈ K := by
-- proof
  apply StatMech.Walls.kc2_faceCorner_in_K he

/--
[kc2_iterate_faceCorner_in_K](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_tailinK.lean)
-/
@[path]
private lemma kc2_iterate_faceCorner_in_K_eq
  {K : Set (Site 2)}
  {e : Dart}
  {k : ℕ}
-- given
  (he : IsBoundaryDart K e) :
-- imply
  kc2_IsCellCorner (dartFace ((dartNext K)^[k] e)) ((dartNext K)^[k] e).tail ∧ ((dartNext K)^[k] e).tail ∈ K := by
-- proof
  apply StatMech.Walls.kc2_iterate_faceCorner_in_K K e he k

/--
[kc2_cellCorner_coord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_tailinK.lean)
-/
@[path]
private lemma kc2_cellCorner_coord_eq
  {f q : Site 2}
-- given
  (h : kc2_IsCellCorner f q) :
-- imply
  (q 0 = f 0 ∨ q 0 = f 0 + 1) ∧ (q 1 = f 1 ∨ q 1 = f 1 + 1) := by
-- proof
  apply StatMech.Walls.kc2_cellCorner_coord h


-- created on 2026-10-23
