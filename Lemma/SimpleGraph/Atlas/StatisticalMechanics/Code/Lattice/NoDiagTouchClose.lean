import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.NoDiagTouchClose
open SimpleGraph Function Set StatMech StatMech.Lattice


/--
[ndt_kingSaturated_product](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/NoDiagTouchClose.lean)
-/
@[path]
private lemma ndt_kingSaturated_product_eq
  {A B : Set ℤ} :
-- imply
  npm_KingSaturated (ndt_product A B) := by
-- proof
  apply StatMech.Lattice.ndt_kingSaturated_product A B

/--
[ndt_box_eq_product](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/NoDiagTouchClose.lean)
-/
@[path]
private lemma ndt_box_eq_product_eq
  {n : ℕ} :
-- imply
  box 2 n = ndt_product {t : ℤ | t.natAbs ≤ n} {t : ℤ | t.natAbs ≤ n} := by
-- proof
  apply StatMech.Lattice.ndt_box_eq_product n

/--
[ndt_kingSaturated_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/NoDiagTouchClose.lean)
-/
@[path]
private lemma ndt_kingSaturated_box_eq
  {n : ℕ} :
-- imply
  npm_KingSaturated (box 2 n) := by
-- proof
  apply StatMech.Lattice.ndt_kingSaturated_box n

/--
[ndt_kingSaturated_sublevel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/NoDiagTouchClose.lean)
-/
@[path]
private lemma ndt_kingSaturated_sublevel_eq
  {φ ψ : ℤ → ℤ}
  {c : ℤ} :
-- imply
  npm_KingSaturated (ndt_sublevel φ ψ c) := by
-- proof
  apply StatMech.Lattice.ndt_kingSaturated_sublevel φ ψ c

/--
[ndt_subset_starHull](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/NoDiagTouchClose.lean)
-/
@[path]
private lemma ndt_subset_starHull_eq
  {K : Set (Site 2)} :
-- imply
  K ⊆ ndt_StarHull K := by
-- proof
  apply StatMech.Lattice.ndt_subset_starHull K

/--
[ndt_kingSaturated_starHull](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/NoDiagTouchClose.lean)
-/
@[path]
private lemma ndt_kingSaturated_starHull_eq
  {K : Set (Site 2)} :
-- imply
  npm_KingSaturated (ndt_StarHull K) := by
-- proof
  apply StatMech.Lattice.ndt_kingSaturated_starHull K

/--
[ndt_noDiagTouch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/NoDiagTouchClose.lean)
-/
@[path]
private lemma ndt_noDiagTouch_eq
  {K : Set (Site 2)} :
-- imply
  npd_NoDiagTouch (ndt_StarHull K) := by
-- proof
  apply StatMech.Lattice.ndt_noDiagTouch K

/--
[ndt_starHull_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/NoDiagTouchClose.lean)
-/
@[path]
private lemma ndt_starHull_empty_eq :
-- imply
  ndt_StarHull (∅ : Set (Site 2)) = ∅ := by
-- proof
  apply StatMech.Lattice.ndt_starHull_empty

/--
[ndt_starHull_subset_of_fillClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/NoDiagTouchClose.lean)
-/
@[path]
private lemma ndt_starHull_subset_of_fillClosed_eq
  {K S : Set (Site 2)}
-- given
  (hKS : K ⊆ S)
  (hS : ndt_FillClosed S) :
-- imply
  ndt_StarHull K ⊆ S := by
-- proof
  apply StatMech.Lattice.ndt_starHull_subset_of_fillClosed hKS hS

/--
[ndt_fillClosed_product](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/NoDiagTouchClose.lean)
-/
@[path]
private lemma ndt_fillClosed_product_eq
  {A B : Set ℤ} :
-- imply
  ndt_FillClosed (ndt_product A B) := by
-- proof
  apply StatMech.Lattice.ndt_fillClosed_product A B

/--
[ndt_starHull_product](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/NoDiagTouchClose.lean)
-/
@[path]
private lemma ndt_starHull_product_eq
  {A B : Set ℤ} :
-- imply
  ndt_StarHull (ndt_product A B) = ndt_product A B := by
-- proof
  apply StatMech.Lattice.ndt_starHull_product A B

/--
[ndt_starHull_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/NoDiagTouchClose.lean)
-/
@[path]
private lemma ndt_starHull_box_eq
  {n : ℕ} :
-- imply
  ndt_StarHull (box 2 n) = box 2 n := by
-- proof
  apply StatMech.Lattice.ndt_starHull_box n

/--
[ndt_faceMultiplicityOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/NoDiagTouchClose.lean)
-/
@[path]
private lemma ndt_faceMultiplicityOne_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}} :
-- imply
  usc_FaceMultiplicityOne (ndt_StarHull K) a := by
-- proof
  apply StatMech.Lattice.ndt_faceMultiplicityOne K a

/--
[ndt_orbitFaceNoPinch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/NoDiagTouchClose.lean)
-/
@[path]
private lemma ndt_orbitFaceNoPinch_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}} :
-- imply
  OrbitFaceNoPinch (ndt_StarHull K) a := by
-- proof
  apply StatMech.Lattice.ndt_orbitFaceNoPinch K a

/--
[ndt_orbit_isCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/NoDiagTouchClose.lean)
-/
@[path]
private lemma ndt_orbit_isCycle_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
-- given
  (hp : 3 ≤ dartOrbitPeriod (ndt_StarHull K) a) :
-- imply
  ((dartOrbitFaceWalk (ndt_StarHull K) a.1 a.2 (dartOrbitPeriod (ndt_StarHull K) a)).copy rfl (by rw [orbit_iterate_period_eq (ndt_StarHull K) a])).IsCycle := by
-- proof
  apply StatMech.Lattice.ndt_orbit_isCycle K a hp

/--
[ndt_box_noDiagTouch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/NoDiagTouchClose.lean)
-/
@[path]
private lemma ndt_box_noDiagTouch_eq
  {n : ℕ} :
-- imply
  npd_NoDiagTouch (box 2 n) := by
-- proof
  apply StatMech.Lattice.ndt_box_noDiagTouch n

/--
[ndt_box_faceMultiplicityOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/NoDiagTouchClose.lean)
-/
@[path]
private lemma ndt_box_faceMultiplicityOne_eq
  {n : ℕ}
  {a : {e : Dart // IsBoundaryDart (box 2 n) e}} :
-- imply
  usc_FaceMultiplicityOne (box 2 n) a := by
-- proof
  apply StatMech.Lattice.ndt_box_faceMultiplicityOne n a

/--
[ndt_box_orbit_isCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/NoDiagTouchClose.lean)
-/
@[path]
private lemma ndt_box_orbit_isCycle_eq
  {n : ℕ}
  {a : {e : Dart // IsBoundaryDart (box 2 n) e}}
-- given
  (hp : 3 ≤ dartOrbitPeriod (box 2 n) a) :
-- imply
  ((dartOrbitFaceWalk (box 2 n) a.1 a.2 (dartOrbitPeriod (box 2 n) a)).copy rfl (by rw [orbit_iterate_period_eq (box 2 n) a])).IsCycle := by
-- proof
  apply StatMech.Lattice.ndt_box_orbit_isCycle n a hp


-- created on 2026-10-23
