import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.NoPinchDual
open SimpleGraph Function Set StatMech StatMech.Lattice


/--
[npd_corners_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/NoPinchDual.lean)
-/
@[path]
private lemma npd_corners_right_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (he : IsBoundaryDart K e)
  (hd : e.dir = ![1, 0]) :
-- imply
  npd_P00 (dartFace e) ∈ K ∧ npd_P10 (dartFace e) ∉ K := by
-- proof
  apply StatMech.Lattice.npd_corners_right he hd

/--
[npd_corners_up](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/NoPinchDual.lean)
-/
@[path]
private lemma npd_corners_up_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (he : IsBoundaryDart K e)
  (hd : e.dir = ![0, 1]) :
-- imply
  npd_P10 (dartFace e) ∈ K ∧ npd_P11 (dartFace e) ∉ K := by
-- proof
  apply StatMech.Lattice.npd_corners_up he hd

/--
[npd_corners_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/NoPinchDual.lean)
-/
@[path]
private lemma npd_corners_left_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (he : IsBoundaryDart K e)
  (hd : e.dir = ![-1, 0]) :
-- imply
  npd_P11 (dartFace e) ∈ K ∧ npd_P01 (dartFace e) ∉ K := by
-- proof
  apply StatMech.Lattice.npd_corners_left he hd

/--
[npd_corners_down](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/NoPinchDual.lean)
-/
@[path]
private lemma npd_corners_down_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (he : IsBoundaryDart K e)
  (hd : e.dir = ![0, -1]) :
-- imply
  npd_P01 (dartFace e) ∈ K ∧ npd_P00 (dartFace e) ∉ K := by
-- proof
  apply StatMech.Lattice.npd_corners_down he hd

/--
[npd_pinch_forces_diagTouch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/NoPinchDual.lean)
-/
@[path]
private lemma npd_pinch_forces_diagTouch_eq
  {K : Set (Site 2)}
  {e₁ e₂ : Dart}
-- given
  (he₁ : IsBoundaryDart K e₁)
  (he₂ : IsBoundaryDart K e₂)
  (hface : dartFace e₁ = dartFace e₂)
  (hdir : e₁.dir ≠ e₂.dir) :
-- imply
  npd_DiagTouch K (dartFace e₁) := by
-- proof
  apply StatMech.Lattice.npd_pinch_forces_diagTouch he₁ he₂ hface hdir

/--
[npd_noPinch_local_of_noDiagTouch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/NoPinchDual.lean)
-/
@[path]
private lemma npd_noPinch_local_of_noDiagTouch_eq
  {K : Set (Site 2)}
  {e₁ e₂ : Dart}
-- given
  (he₁ : IsBoundaryDart K e₁)
  (he₂ : IsBoundaryDart K e₂)
  (hface : dartFace e₁ = dartFace e₂)
  (hnt : ¬ npd_DiagTouch K (dartFace e₁)) :
-- imply
  e₁.dir = e₂.dir := by
-- proof
  apply StatMech.Lattice.npd_noPinch_local_of_noDiagTouch he₁ he₂ hface hnt

/--
[npd_dart_eq_of_noDiagTouch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/NoPinchDual.lean)
-/
@[path]
private lemma npd_dart_eq_of_noDiagTouch_eq
  {K : Set (Site 2)}
  {e₁ e₂ : Dart}
-- given
  (he₁ : IsBoundaryDart K e₁)
  (he₂ : IsBoundaryDart K e₂)
  (hface : dartFace e₁ = dartFace e₂)
  (hnt : ¬ npd_DiagTouch K (dartFace e₁)) :
-- imply
  e₁ = e₂ := by
-- proof
  apply StatMech.Lattice.npd_dart_eq_of_noDiagTouch he₁ he₂ hface hnt

/--
[npd_orbitFaceNoPinch_of_noDiagTouch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/NoPinchDual.lean)
-/
@[path]
private lemma npd_orbitFaceNoPinch_of_noDiagTouch_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (h : npd_NoDiagTouchAlongOrbit K a) :
-- imply
  OrbitFaceNoPinch K a := by
-- proof
  apply StatMech.Lattice.npd_orbitFaceNoPinch_of_noDiagTouch K a h

/--
[npd_orbitFace_injOn_of_noDiagTouch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/NoPinchDual.lean)
-/
@[path]
private lemma npd_orbitFace_injOn_of_noDiagTouch_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (h : npd_NoDiagTouchAlongOrbit K a) :
-- imply
  Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1)) (Set.Iio (dartOrbitPeriod K a)) := by
-- proof
  apply StatMech.Lattice.npd_orbitFace_injOn_of_noDiagTouch K a h

/--
[npd_noDiagTouchAlongOrbit_of_global](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/NoPinchDual.lean)
-/
@[path]
private lemma npd_noDiagTouchAlongOrbit_of_global_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (h : npd_NoDiagTouch K) :
-- imply
  npd_NoDiagTouchAlongOrbit K a := by
-- proof
  apply StatMech.Lattice.npd_noDiagTouchAlongOrbit_of_global h a

/--
[npd_orbitFaceNoPinch_of_globalNoDiagTouch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/NoPinchDual.lean)
-/
@[path]
private lemma npd_orbitFaceNoPinch_of_globalNoDiagTouch_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (h : npd_NoDiagTouch K) :
-- imply
  OrbitFaceNoPinch K a := by
-- proof
  apply StatMech.Lattice.npd_orbitFaceNoPinch_of_globalNoDiagTouch K a h

/--
[npd_diagTouch_example](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/NoPinchDual.lean)
-/
@[path]
private lemma npd_diagTouch_example_eq :
-- imply
  npd_DiagTouch ({![0, 0], ![1, 1]} : Set (Site 2)) ![0, 0] := by
-- proof
  apply StatMech.Lattice.npd_diagTouch_example


-- created on 2026-10-23
