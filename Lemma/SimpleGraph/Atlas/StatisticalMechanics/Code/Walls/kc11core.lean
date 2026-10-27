import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.kc11core
open Set SimpleGraph Function StatMech StatMech.Walls


/--
[kc11_face_dir_unique_of_noDiagTouch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc11core.lean)
-/
@[path]
private lemma kc11_face_dir_unique_of_noDiagTouch_eq
  {K : Set (Site 2)}
  {e₁ e₂ : Dart}
-- given
  (hnt : npd_NoDiagTouch K)
  (he₁ : IsBoundaryDart K e₁)
  (he₂ : IsBoundaryDart K e₂)
  (hface : dartFace e₁ = dartFace e₂) :
-- imply
  e₁.dir = e₂.dir := by
-- proof
  apply StatMech.Walls.kc11_face_dir_unique_of_noDiagTouch hnt he₁ he₂ hface

/--
[kc11_dart_eq_of_noDiagTouch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc11core.lean)
-/
@[path]
private lemma kc11_dart_eq_of_noDiagTouch_eq
  {K : Set (Site 2)}
  {e₁ e₂ : Dart}
-- given
  (hnt : npd_NoDiagTouch K)
  (he₁ : IsBoundaryDart K e₁)
  (he₂ : IsBoundaryDart K e₂)
  (hface : dartFace e₁ = dartFace e₂) :
-- imply
  e₁ = e₂ := by
-- proof
  apply StatMech.Walls.kc11_dart_eq_of_noDiagTouch hnt he₁ he₂ hface

/--
[kc11_support_dart_dir_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc11core.lean)
-/
@[path]
private lemma kc11_support_dart_dir_unique_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {z : Site 2}
  {i j : ℕ}
-- given
  (hnt : npd_NoDiagTouch K)
  (hi : z = dartFace ((dartNext K)^[i] a.1))
  (hj : z = dartFace ((dartNext K)^[j] a.1)) :
-- imply
  ((dartNext K)^[i] a.1).dir = ((dartNext K)^[j] a.1).dir := by
-- proof
  apply StatMech.Walls.kc11_support_dart_dir_unique hnt a hi hj

/--
[kc11_collarSlide_of_noDiagTouch_and_escape](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc11core.lean)
-/
@[path]
private lemma kc11_collarSlide_of_noDiagTouch_and_escape_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {R : ℕ}
-- given
  (_hnt : npd_NoDiagTouch K)
  (hsupp : oc_supportSet (mpl_orbitLoop K a) ⊆ box 2 R)
  (hesc : kc5_OffSupportReachesExterior (mpl_orbitLoop K a) R) :
-- imply
  kc10_CollarSlide (mpl_orbitLoop K a) R := by
-- proof
  apply StatMech.Walls.kc11_collarSlide_of_noDiagTouch_and_escape a R _hnt hsupp hesc

/--
[kc11_collarSlide_of_escape](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc11core.lean)
-/
@[path]
private lemma kc11_collarSlide_of_escape_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hesc : kc5_OffSupportReachesExterior Vc R) :
-- imply
  kc10_CollarSlide Vc R := by
-- proof
  apply StatMech.Walls.kc11_collarSlide_of_escape Vc R hsupp hesc

/--
[kc11_starHull_noDiagTouch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc11core.lean)
-/
@[path]
private lemma kc11_starHull_noDiagTouch_eq
  {K : Set (Site 2)} :
-- imply
  npd_NoDiagTouch (ndt_StarHull K) := by
-- proof
  apply StatMech.Walls.kc11_starHull_noDiagTouch K

/--
[kc11_starHull_face_dir_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc11core.lean)
-/
@[path]
private lemma kc11_starHull_face_dir_unique_eq
  {K : Set (Site 2)}
  {e₁ e₂ : Dart}
-- given
  (he₁ : IsBoundaryDart (ndt_StarHull K) e₁)
  (he₂ : IsBoundaryDart (ndt_StarHull K) e₂)
  (hface : dartFace e₁ = dartFace e₂) :
-- imply
  e₁.dir = e₂.dir := by
-- proof
  apply StatMech.Walls.kc11_starHull_face_dir_unique K he₁ he₂ hface

/--
[kc11_starHull_collarSlide_of_escape](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc11core.lean)
-/
@[path]
private lemma kc11_starHull_collarSlide_of_escape_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
  {R : ℕ}
-- given
  (hsupp : oc_supportSet (mpl_orbitLoop (ndt_StarHull K) a) ⊆ box 2 R)
  (hesc : kc5_OffSupportReachesExterior (mpl_orbitLoop (ndt_StarHull K) a) R) :
-- imply
  kc10_CollarSlide (mpl_orbitLoop (ndt_StarHull K) a) R := by
-- proof
  apply StatMech.Walls.kc11_starHull_collarSlide_of_escape K a R hsupp hesc

/--
[kc11_unitCell_collarSlide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc11core.lean)
-/
@[path]
private lemma kc11_unitCell_collarSlide_eq :
-- imply
  kc10_CollarSlide (mpl_orbitLoop unitCell ucBase) 1 := by
-- proof
  apply StatMech.Walls.kc11_unitCell_collarSlide


-- created on 2026-10-23
