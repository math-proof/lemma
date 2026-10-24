import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.kc2_leftupfacecell
open SimpleGraph Function Set StatMech StatMech.Walls


/--
[kc2_P00_eq_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_leftupfacecell.lean)
-/
@[path]
private lemma kc2_P00_eq_self_eq
  {f : Site 2} :
-- imply
  npd_P00 f = f := by
-- proof
  apply StatMech.Walls.kc2_P00_eq_self f

/--
[kc2_leftDart_face](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_leftupfacecell.lean)
-/
@[path]
private lemma kc2_leftDart_face_eq
  {e : Dart}
-- given
  (hd : e.dir = ![-1, 0]) :
-- imply
  dartFace e = ![e.tail 0 - 1, e.tail 1 - 1] := by
-- proof
  apply StatMech.Walls.kc2_leftDart_face e hd

/--
[kc2_leftDart_tail_eq_P11](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_leftupfacecell.lean)
-/
@[path]
private lemma kc2_leftDart_tail_eq_P11_eq
  {e : Dart}
-- given
  (hd : e.dir = ![-1, 0]) :
-- imply
  e.tail = npd_P11 (dartFace e) := by
-- proof
  apply StatMech.Walls.kc2_leftDart_tail_eq_P11 e hd

/--
[kc2_leftDart_head_eq_P01](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_leftupfacecell.lean)
-/
@[path]
private lemma kc2_leftDart_head_eq_P01_eq
  {e : Dart}
-- given
  (hd : e.dir = ![-1, 0]) :
-- imply
  e.head = npd_P01 (dartFace e) := by
-- proof
  apply StatMech.Walls.kc2_leftDart_head_eq_P01 e hd

/--
[kc2_leftDart_corners](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_leftupfacecell.lean)
-/
@[path]
private lemma kc2_leftDart_corners_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (he : IsBoundaryDart K e)
  (hd : e.dir = ![-1, 0]) :
-- imply
  npd_P11 (dartFace e) ∈ K ∧ npd_P01 (dartFace e) ∉ K := by
-- proof
  apply StatMech.Walls.kc2_leftDart_corners he hd

/--
[kc2_upDart_face](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_leftupfacecell.lean)
-/
@[path]
private lemma kc2_upDart_face_eq
  {e : Dart}
-- given
  (hd : e.dir = ![0, 1]) :
-- imply
  dartFace e = ![e.tail 0 - 1, e.tail 1] := by
-- proof
  apply StatMech.Walls.kc2_upDart_face e hd

/--
[kc2_upDart_tail_eq_P10](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_leftupfacecell.lean)
-/
@[path]
private lemma kc2_upDart_tail_eq_P10_eq
  {e : Dart}
-- given
  (hd : e.dir = ![0, 1]) :
-- imply
  e.tail = npd_P10 (dartFace e) := by
-- proof
  apply StatMech.Walls.kc2_upDart_tail_eq_P10 e hd

/--
[kc2_upDart_head_eq_P11](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_leftupfacecell.lean)
-/
@[path]
private lemma kc2_upDart_head_eq_P11_eq
  {e : Dart}
-- given
  (hd : e.dir = ![0, 1]) :
-- imply
  e.head = npd_P11 (dartFace e) := by
-- proof
  apply StatMech.Walls.kc2_upDart_head_eq_P11 e hd

/--
[kc2_upDart_corners](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_leftupfacecell.lean)
-/
@[path]
private lemma kc2_upDart_corners_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (he : IsBoundaryDart K e)
  (hd : e.dir = ![0, 1]) :
-- imply
  npd_P10 (dartFace e) ∈ K ∧ npd_P11 (dartFace e) ∉ K := by
-- proof
  apply StatMech.Walls.kc2_upDart_corners he hd

/--
[kc2_P00_ne_P11](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_leftupfacecell.lean)
-/
@[path]
private lemma kc2_P00_ne_P11_eq
  {f : Site 2} :
-- imply
  npd_P00 f ≠ npd_P11 f := by
-- proof
  apply StatMech.Walls.kc2_P00_ne_P11 f

/--
[kc2_P00_ne_P10](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_leftupfacecell.lean)
-/
@[path]
private lemma kc2_P00_ne_P10_eq
  {f : Site 2} :
-- imply
  npd_P00 f ≠ npd_P10 f := by
-- proof
  apply StatMech.Walls.kc2_P00_ne_P10 f

/--
[kc2_leftDart_face_ne_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_leftupfacecell.lean)
-/
@[path]
private lemma kc2_leftDart_face_ne_tail_eq
  {e : Dart}
-- given
  (hd : e.dir = ![-1, 0]) :
-- imply
  dartFace e ≠ e.tail := by
-- proof
  apply StatMech.Walls.kc2_leftDart_face_ne_tail e hd

/--
[kc2_upDart_face_ne_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_leftupfacecell.lean)
-/
@[path]
private lemma kc2_upDart_face_ne_tail_eq
  {e : Dart}
-- given
  (hd : e.dir = ![0, 1]) :
-- imply
  dartFace e ≠ e.tail := by
-- proof
  apply StatMech.Walls.kc2_upDart_face_ne_tail e hd

/--
[kc2_leftUp_faceCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_leftupfacecell.lean)
-/
@[path]
private lemma kc2_leftUp_faceCell_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (he : IsBoundaryDart K e)
  (hdir : e.dir = ![-1, 0] ∨ e.dir = ![0, 1]) :
-- imply
  dartFace e = npd_P00 (dartFace e) ∧ npd_P00 (dartFace e) ≠ e.tail ∧ ( (e.dir = ![-1, 0] ∧ dartFace e = ![e.tail 0 - 1, e.tail 1 - 1] ∧ e.tail = npd_P11 (dartFace e) ∧ npd_P11 (dartFace e) ∈ K) ∨ (e.dir = ![0, 1] ∧ dartFace e = ![e.tail 0 - 1, e.tail 1] ∧ e.tail = npd_P10 (dartFace e) ∧ npd_P10 (dartFace e) ∈ K) ) := by
-- proof
  apply StatMech.Walls.kc2_leftUp_faceCell he hdir

/--
[kc2_dir_trichotomy_faceCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_leftupfacecell.lean)
-/
@[path]
private lemma kc2_dir_trichotomy_faceCell_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (he : IsBoundaryDart K e) :
-- imply
  e.dir = ![1, 0] ∨ e.dir = ![0, -1] ∨ (dartFace e = npd_P00 (dartFace e) ∧ npd_P00 (dartFace e) ≠ e.tail) := by
-- proof
  apply StatMech.Walls.kc2_dir_trichotomy_faceCell he

/--
[kc2_witLeftDart_dir](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_leftupfacecell.lean)
-/
@[path]
private lemma kc2_witLeftDart_dir_eq :
-- imply
  kc2_witLeftDart.dir = ![-1, 0] := by
-- proof
  apply StatMech.Walls.kc2_witLeftDart_dir

/--
[kc2_witLeftDart_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_leftupfacecell.lean)
-/
@[path]
private lemma kc2_witLeftDart_tail_eq :
-- imply
  kc2_witLeftDart.tail = ![1, 1] := by
-- proof
  apply StatMech.Walls.kc2_witLeftDart_tail

/--
[kc2_witLeftDart_face](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_leftupfacecell.lean)
-/
@[path]
private lemma kc2_witLeftDart_face_eq :
-- imply
  dartFace kc2_witLeftDart = ![0, 0] := by
-- proof
  apply StatMech.Walls.kc2_witLeftDart_face

/--
[kc2_witLeftDart_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_leftupfacecell.lean)
-/
@[path]
private lemma kc2_witLeftDart_head_eq :
-- imply
  kc2_witLeftDart.head = ![0, 1] := by
-- proof
  apply StatMech.Walls.kc2_witLeftDart_head

/--
[kc2_witLeftDart_boundary_K1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_leftupfacecell.lean)
-/
@[path]
private lemma kc2_witLeftDart_boundary_K1_eq :
-- imply
  IsBoundaryDart ({![1, 1]} : Set (Site 2)) kc2_witLeftDart := by
-- proof
  apply StatMech.Walls.kc2_witLeftDart_boundary_K1

/--
[kc2_witLeftDart_boundary_K2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_leftupfacecell.lean)
-/
@[path]
private lemma kc2_witLeftDart_boundary_K2_eq :
-- imply
  IsBoundaryDart ({![0, 0], ![1, 1]} : Set (Site 2)) kc2_witLeftDart := by
-- proof
  apply StatMech.Walls.kc2_witLeftDart_boundary_K2

/--
[kc2_witLeftDart_P00_notin_K1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_leftupfacecell.lean)
-/
@[path]
private lemma kc2_witLeftDart_P00_notin_K1_eq :
-- imply
  npd_P00 (dartFace kc2_witLeftDart) ∉ ({![1, 1]} : Set (Site 2)) := by
-- proof
  apply StatMech.Walls.kc2_witLeftDart_P00_notin_K1

/--
[kc2_witLeftDart_P00_in_K2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_leftupfacecell.lean)
-/
@[path]
private lemma kc2_witLeftDart_P00_in_K2_eq :
-- imply
  npd_P00 (dartFace kc2_witLeftDart) ∈ ({![0, 0], ![1, 1]} : Set (Site 2)) := by
-- proof
  apply StatMech.Walls.kc2_witLeftDart_P00_in_K2

/--
[kc2_face_membership_not_pinned](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_leftupfacecell.lean)
-/
@[path]
private lemma kc2_face_membership_not_pinned_eq :
-- imply
  ∃ (e : Dart) (K₁ K₂ : Set (Site 2)), IsBoundaryDart K₁ e ∧ IsBoundaryDart K₂ e ∧ npd_P00 (dartFace e) ∉ K₁ ∧ npd_P00 (dartFace e) ∈ K₂ := by
-- proof
  apply StatMech.Walls.kc2_face_membership_not_pinned


-- created on 2026-10-23
