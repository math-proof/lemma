import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.kc3_upleftfacecell.Part3
open SimpleGraph Function Set StatMech StatMech.Walls


/--
[kc3_upDart_face](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_upleftfacecell.lean)
-/
@[path]
private lemma kc3_upDart_face_eq
  {e : Dart}
-- given
  (hd : e.dir = ![0, 1]) :
-- imply
  dartFace e = ![e.tail 0 - 1, e.tail 1] := by
-- proof
  apply StatMech.Walls.kc3_upDart_face e hd

/--
[kc3_upDart_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_upleftfacecell.lean)
-/
@[path]
private lemma kc3_upDart_tail_eq
  {e : Dart}
-- given
  (hd : e.dir = ![0, 1]) :
-- imply
  e.tail = ![dartFace e 0 + 1, dartFace e 1] := by
-- proof
  apply StatMech.Walls.kc3_upDart_tail e hd

/--
[kc3_upDart_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_upleftfacecell.lean)
-/
@[path]
private lemma kc3_upDart_head_eq
  {e : Dart}
-- given
  (hd : e.dir = ![0, 1]) :
-- imply
  e.head = ![dartFace e 0 + 1, dartFace e 1 + 1] := by
-- proof
  apply StatMech.Walls.kc3_upDart_head e hd

/--
[kc3_upDart_face_ne_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_upleftfacecell.lean)
-/
@[path]
private lemma kc3_upDart_face_ne_tail_eq
  {e : Dart}
-- given
  (hd : e.dir = ![0, 1]) :
-- imply
  dartFace e ≠ e.tail := by
-- proof
  apply StatMech.Walls.kc3_upDart_face_ne_tail e hd

/--
[kc3_upDart_face_ne_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_upleftfacecell.lean)
-/
@[path]
private lemma kc3_upDart_face_ne_head_eq
  {e : Dart}
-- given
  (hd : e.dir = ![0, 1]) :
-- imply
  dartFace e ≠ e.head := by
-- proof
  apply StatMech.Walls.kc3_upDart_face_ne_head e hd

/--
[kc3_leftDart_face](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_upleftfacecell.lean)
-/
@[path]
private lemma kc3_leftDart_face_eq
  {e : Dart}
-- given
  (hd : e.dir = ![-1, 0]) :
-- imply
  dartFace e = ![e.tail 0 - 1, e.tail 1 - 1] := by
-- proof
  apply StatMech.Walls.kc3_leftDart_face e hd

/--
[kc3_leftDart_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_upleftfacecell.lean)
-/
@[path]
private lemma kc3_leftDart_tail_eq
  {e : Dart}
-- given
  (hd : e.dir = ![-1, 0]) :
-- imply
  e.tail = ![dartFace e 0 + 1, dartFace e 1 + 1] := by
-- proof
  apply StatMech.Walls.kc3_leftDart_tail e hd

/--
[kc3_leftDart_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_upleftfacecell.lean)
-/
@[path]
private lemma kc3_leftDart_head_eq
  {e : Dart}
-- given
  (hd : e.dir = ![-1, 0]) :
-- imply
  e.head = ![dartFace e 0, dartFace e 1 + 1] := by
-- proof
  apply StatMech.Walls.kc3_leftDart_head e hd

/--
[kc3_leftDart_face_ne_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_upleftfacecell.lean)
-/
@[path]
private lemma kc3_leftDart_face_ne_tail_eq
  {e : Dart}
-- given
  (hd : e.dir = ![-1, 0]) :
-- imply
  dartFace e ≠ e.tail := by
-- proof
  apply StatMech.Walls.kc3_leftDart_face_ne_tail e hd

/--
[kc3_leftDart_face_ne_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_upleftfacecell.lean)
-/
@[path]
private lemma kc3_leftDart_face_ne_head_eq
  {e : Dart}
-- given
  (hd : e.dir = ![-1, 0]) :
-- imply
  dartFace e ≠ e.head := by
-- proof
  apply StatMech.Walls.kc3_leftDart_face_ne_head e hd

/--
[kc3_upLeft_faceCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_upleftfacecell.lean)
-/
@[path]
private lemma kc3_upLeft_faceCell_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (he : IsBoundaryDart K e)
  (hdir : e.dir = ![0, 1] ∨ e.dir = ![-1, 0]) :
-- imply
  dartFace e ≠ e.tail ∧ dartFace e ≠ e.head ∧ e.tail ∈ K ∧ e.head ∉ K ∧ ( (e.dir = ![0, 1] ∧ dartFace e = ![e.tail 0 - 1, e.tail 1] ∧ e.tail = ![dartFace e 0 + 1, dartFace e 1]) ∨ (e.dir = ![-1, 0] ∧ dartFace e = ![e.tail 0 - 1, e.tail 1 - 1] ∧ e.tail = ![dartFace e 0 + 1, dartFace e 1 + 1]) ) := by
-- proof
  apply StatMech.Walls.kc3_upLeft_faceCell he hdir

/--
[kc3_dir_trichotomy_faceCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_upleftfacecell.lean)
-/
@[path]
private lemma kc3_dir_trichotomy_faceCell_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (_he : IsBoundaryDart K e) :
-- imply
  e.dir = ![1, 0] ∨ e.dir = ![0, -1] ∨ (dartFace e ≠ e.tail ∧ dartFace e ≠ e.head) := by
-- proof
  apply StatMech.Walls.kc3_dir_trichotomy_faceCell _he

/--
[kc3_ul_witUpDart_dir](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_upleftfacecell.lean)
-/
@[path]
private lemma kc3_ul_witUpDart_dir_eq :
-- imply
  kc3_ul_witUpDart.dir = ![0, 1] := by
-- proof
  apply StatMech.Walls.kc3_ul_witUpDart_dir

/--
[kc3_ul_witUpDart_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_upleftfacecell.lean)
-/
@[path]
private lemma kc3_ul_witUpDart_tail_eq :
-- imply
  kc3_ul_witUpDart.tail = ![1, 0] := by
-- proof
  apply StatMech.Walls.kc3_ul_witUpDart_tail

/--
[kc3_ul_witUpDart_face](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_upleftfacecell.lean)
-/
@[path]
private lemma kc3_ul_witUpDart_face_eq :
-- imply
  dartFace kc3_ul_witUpDart = ![0, 0] := by
-- proof
  apply StatMech.Walls.kc3_ul_witUpDart_face

/--
[kc3_ul_witUpDart_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_upleftfacecell.lean)
-/
@[path]
private lemma kc3_ul_witUpDart_head_eq :
-- imply
  kc3_ul_witUpDart.head = ![1, 1] := by
-- proof
  apply StatMech.Walls.kc3_ul_witUpDart_head

/--
[kc3_ul_witUpDart_boundary_K1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_upleftfacecell.lean)
-/
@[path]
private lemma kc3_ul_witUpDart_boundary_K1_eq :
-- imply
  IsBoundaryDart ({![1, 0]} : Set (Site 2)) kc3_ul_witUpDart := by
-- proof
  apply StatMech.Walls.kc3_ul_witUpDart_boundary_K1

/--
[kc3_ul_witUpDart_boundary_K2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_upleftfacecell.lean)
-/
@[path]
private lemma kc3_ul_witUpDart_boundary_K2_eq :
-- imply
  IsBoundaryDart ({![0, 0], ![1, 0]} : Set (Site 2)) kc3_ul_witUpDart := by
-- proof
  apply StatMech.Walls.kc3_ul_witUpDart_boundary_K2

/--
[kc3_ul_witUpDart_face_notin_K1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_upleftfacecell.lean)
-/
@[path]
private lemma kc3_ul_witUpDart_face_notin_K1_eq :
-- imply
  dartFace kc3_ul_witUpDart ∉ ({![1, 0]} : Set (Site 2)) := by
-- proof
  apply StatMech.Walls.kc3_ul_witUpDart_face_notin_K1

/--
[kc3_ul_witUpDart_face_in_K2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_upleftfacecell.lean)
-/
@[path]
private lemma kc3_ul_witUpDart_face_in_K2_eq :
-- imply
  dartFace kc3_ul_witUpDart ∈ ({![0, 0], ![1, 0]} : Set (Site 2)) := by
-- proof
  apply StatMech.Walls.kc3_ul_witUpDart_face_in_K2

/--
[kc3_ul_witLeftDart_dir](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_upleftfacecell.lean)
-/
@[path]
private lemma kc3_ul_witLeftDart_dir_eq :
-- imply
  kc3_ul_witLeftDart.dir = ![-1, 0] := by
-- proof
  apply StatMech.Walls.kc3_ul_witLeftDart_dir

/--
[kc3_ul_witLeftDart_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_upleftfacecell.lean)
-/
@[path]
private lemma kc3_ul_witLeftDart_tail_eq :
-- imply
  kc3_ul_witLeftDart.tail = ![1, 1] := by
-- proof
  apply StatMech.Walls.kc3_ul_witLeftDart_tail

/--
[kc3_ul_witLeftDart_face](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_upleftfacecell.lean)
-/
@[path]
private lemma kc3_ul_witLeftDart_face_eq :
-- imply
  dartFace kc3_ul_witLeftDart = ![0, 0] := by
-- proof
  apply StatMech.Walls.kc3_ul_witLeftDart_face

/--
[kc3_ul_witLeftDart_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_upleftfacecell.lean)
-/
@[path]
private lemma kc3_ul_witLeftDart_head_eq :
-- imply
  kc3_ul_witLeftDart.head = ![0, 1] := by
-- proof
  apply StatMech.Walls.kc3_ul_witLeftDart_head

/--
[kc3_ul_witLeftDart_boundary_K1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_upleftfacecell.lean)
-/
@[path]
private lemma kc3_ul_witLeftDart_boundary_K1_eq :
-- imply
  IsBoundaryDart ({![1, 1]} : Set (Site 2)) kc3_ul_witLeftDart := by
-- proof
  apply StatMech.Walls.kc3_ul_witLeftDart_boundary_K1

/--
[kc3_ul_witLeftDart_boundary_K2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_upleftfacecell.lean)
-/
@[path]
private lemma kc3_ul_witLeftDart_boundary_K2_eq :
-- imply
  IsBoundaryDart ({![0, 0], ![1, 1]} : Set (Site 2)) kc3_ul_witLeftDart := by
-- proof
  apply StatMech.Walls.kc3_ul_witLeftDart_boundary_K2

/--
[kc3_ul_witLeftDart_face_notin_K1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_upleftfacecell.lean)
-/
@[path]
private lemma kc3_ul_witLeftDart_face_notin_K1_eq :
-- imply
  dartFace kc3_ul_witLeftDart ∉ ({![1, 1]} : Set (Site 2)) := by
-- proof
  apply StatMech.Walls.kc3_ul_witLeftDart_face_notin_K1

/--
[kc3_ul_witLeftDart_face_in_K2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_upleftfacecell.lean)
-/
@[path]
private lemma kc3_ul_witLeftDart_face_in_K2_eq :
-- imply
  dartFace kc3_ul_witLeftDart ∈ ({![0, 0], ![1, 1]} : Set (Site 2)) := by
-- proof
  apply StatMech.Walls.kc3_ul_witLeftDart_face_in_K2

/--
[kc3_face_membership_unpinned_up](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_upleftfacecell.lean)
-/
@[path]
private lemma kc3_face_membership_unpinned_up_eq :
-- imply
  ∃ (e : Dart) (K₁ K₂ : Set (Site 2)), e.dir = ![0, 1] ∧ IsBoundaryDart K₁ e ∧ IsBoundaryDart K₂ e ∧ dartFace e ∉ K₁ ∧ dartFace e ∈ K₂ := by
-- proof
  apply StatMech.Walls.kc3_face_membership_unpinned_up

/--
[kc3_face_membership_unpinned_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_upleftfacecell.lean)
-/
@[path]
private lemma kc3_face_membership_unpinned_left_eq :
-- imply
  ∃ (e : Dart) (K₁ K₂ : Set (Site 2)), e.dir = ![-1, 0] ∧ IsBoundaryDart K₁ e ∧ IsBoundaryDart K₂ e ∧ dartFace e ∉ K₁ ∧ dartFace e ∈ K₂ := by
-- proof
  apply StatMech.Walls.kc3_face_membership_unpinned_left

/--
[kc3_face_membership_unpinned](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_upleftfacecell.lean)
-/
@[path]
private lemma kc3_face_membership_unpinned_eq :
-- imply
  (∃ (e : Dart) (K₁ K₂ : Set (Site 2)), e.dir = ![0, 1] ∧ IsBoundaryDart K₁ e ∧ IsBoundaryDart K₂ e ∧ dartFace e ∉ K₁ ∧ dartFace e ∈ K₂) ∧ (∃ (e : Dart) (K₁ K₂ : Set (Site 2)), e.dir = ![-1, 0] ∧ IsBoundaryDart K₁ e ∧ IsBoundaryDart K₂ e ∧ dartFace e ∉ K₁ ∧ dartFace e ∈ K₂) := by
-- proof
  apply StatMech.Walls.kc3_face_membership_unpinned


-- created on 2026-10-23
