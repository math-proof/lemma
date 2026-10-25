import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.kc2_rightfaceinK
open Set SimpleGraph StatMech StatMech.Walls


/--
[kc2_dartDir_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_rightfaceinK.lean)
-/
@[path]
private lemma kc2_dartDir_cases_eq
  {e : Dart} :
-- imply
  e.dir = ![1, 0] ∨ e.dir = ![-1, 0] ∨ e.dir = ![0, 1] ∨ e.dir = ![0, -1] := by
-- proof
  apply StatMech.Walls.kc2_dartDir_cases e

/--
[kc2_etaExpand_site2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_rightfaceinK.lean)
-/
@[path]
private lemma kc2_etaExpand_site2_eq
  {z : Site 2} :
-- imply
  z = ![z 0, z 1] := by
-- proof
  apply StatMech.Walls.kc2_etaExpand_site2 z

/--
[kc2_dartFace_eq_tail_of_dir_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_rightfaceinK.lean)
-/
@[path]
private lemma kc2_dartFace_eq_tail_of_dir_right_eq
  {e : Dart}
-- given
  (hd : e.dir = ![1, 0]) :
-- imply
  dartFace e = e.tail := by
-- proof
  apply StatMech.Walls.kc2_dartFace_eq_tail_of_dir_right e hd

/--
[kc2_rightDart_face_mem_of_tail_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_rightfaceinK.lean)
-/
@[path]
private lemma kc2_rightDart_face_mem_of_tail_mem_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hd : e.dir = ![1, 0])
  (htail : e.tail ∈ K) :
-- imply
  dartFace e ∈ K := by
-- proof
  apply StatMech.Walls.kc2_rightDart_face_mem_of_tail_mem K e hd htail

/--
[kc2_rightDart_face_mem_K](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_rightfaceinK.lean)
-/
@[path]
private lemma kc2_rightDart_face_mem_K_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (he : IsBoundaryDart K e)
  (hd : e.dir = ![1, 0]) :
-- imply
  dartFace e ∈ K := by
-- proof
  apply StatMech.Walls.kc2_rightDart_face_mem_K K e he hd

/--
[kc2_rightDart_supportOdd_in_K](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_rightfaceinK.lean)
-/
@[path]
private lemma kc2_rightDart_supportOdd_in_K_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (he : IsBoundaryDart K e)
  (hd : e.dir = ![1, 0])
  (P : Prop) :
-- imply
  P → dartFace e ∈ K := by
-- proof
  apply StatMech.Walls.kc2_rightDart_supportOdd_in_K K e he hd P


-- created on 2026-10-23
