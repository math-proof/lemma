import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Lattice.Wall1EmbeddingRetry
open SimpleGraph Function Set Finset StatMech StatMech.Lattice


/--
[emb_twoVisit_pinch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Wall1EmbeddingRetry.lean)
-/
@[path]
private lemma emb_twoVisit_pinch_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {f : Site 2}
  {i j : ℕ}
-- given
  (hi : i ∈ usc_visitSet K a f)
  (hj : j ∈ usc_visitSet K a f)
  (hij : i ≠ j) :
-- imply
  dartFace ((dartNext K)^[i] a.1) = dartFace ((dartNext K)^[j] a.1) ∧ ((dartNext K)^[i] a.1).dir ≠ ((dartNext K)^[j] a.1).dir := by
-- proof
  apply StatMech.Lattice.emb_twoVisit_pinch K a f hi hj hij

/--
[emb_twoVisit_forces_diagTouch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Wall1EmbeddingRetry.lean)
-/
@[path]
private lemma emb_twoVisit_forces_diagTouch_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {f : Site 2}
  {i j : ℕ}
-- given
  (hi : i ∈ usc_visitSet K a f)
  (hj : j ∈ usc_visitSet K a f)
  (hij : i ≠ j) :
-- imply
  npd_DiagTouch K f := by
-- proof
  apply StatMech.Lattice.emb_twoVisit_forces_diagTouch K a f hi hj hij

/--
[emb_visit_le_one_of_noDiagTouch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Wall1EmbeddingRetry.lean)
-/
@[path]
private lemma emb_visit_le_one_of_noDiagTouch_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {f : Site 2}
-- given
  (h : npd_NoDiagTouch K) :
-- imply
  (usc_visitSet K a f).card ≤ 1 := by
-- proof
  apply StatMech.Lattice.emb_visit_le_one_of_noDiagTouch K a h f

/--
[emb_faceMultiplicityOne_of_noDiagTouch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Wall1EmbeddingRetry.lean)
-/
@[path]
private lemma emb_faceMultiplicityOne_of_noDiagTouch_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (h : npd_NoDiagTouch K) :
-- imply
  usc_FaceMultiplicityOne K a := by
-- proof
  apply StatMech.Lattice.emb_faceMultiplicityOne_of_noDiagTouch K a h

/--
[emb_faceMultiplicityOne_of_kingSaturated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Wall1EmbeddingRetry.lean)
-/
@[path]
private lemma emb_faceMultiplicityOne_of_kingSaturated_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (h : npm_KingSaturated K) :
-- imply
  usc_FaceMultiplicityOne K a := by
-- proof
  apply StatMech.Lattice.emb_faceMultiplicityOne_of_kingSaturated K a h

/--
[emb_fullUnitCell_faceMultiplicityOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Wall1EmbeddingRetry.lean)
-/
@[path]
private lemma emb_fullUnitCell_faceMultiplicityOne_eq
  {a : {e : Dart // IsBoundaryDart ({![0, 0], ![1, 0], ![0, 1], ![1, 1]} : Set (Site 2)) e}} :
-- imply
  usc_FaceMultiplicityOne ({![0, 0], ![1, 0], ![0, 1], ![1, 1]} : Set (Site 2)) a := by
-- proof
  apply StatMech.Lattice.emb_fullUnitCell_faceMultiplicityOne a

/--
[emb_unitCell_faceMultiplicityOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Wall1EmbeddingRetry.lean)
-/
@[path]
private lemma emb_unitCell_faceMultiplicityOne_eq :
-- imply
  usc_FaceMultiplicityOne unitCell ucBase := by
-- proof
  apply StatMech.Lattice.emb_unitCell_faceMultiplicityOne

/--
[emb_domino_faceMultiplicityOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Wall1EmbeddingRetry.lean)
-/
@[path]
private lemma emb_domino_faceMultiplicityOne_eq :
-- imply
  usc_FaceMultiplicityOne domino dmBase := by
-- proof
  apply StatMech.Lattice.emb_domino_faceMultiplicityOne

/--
[emb_orbitFaceNoPinch_of_noDiagTouch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Wall1EmbeddingRetry.lean)
-/
@[path]
private lemma emb_orbitFaceNoPinch_of_noDiagTouch_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (h : npd_NoDiagTouch K) :
-- imply
  OrbitFaceNoPinch K a := by
-- proof
  apply StatMech.Lattice.emb_orbitFaceNoPinch_of_noDiagTouch K a h

/--
[emb_orbit_isCycle_of_noDiagTouch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Wall1EmbeddingRetry.lean)
-/
@[path]
private lemma emb_orbit_isCycle_of_noDiagTouch_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hp : 3 ≤ dartOrbitPeriod K a)
  (h : npd_NoDiagTouch K) :
-- imply
  ((dartOrbitFaceWalk K a.1 a.2 (dartOrbitPeriod K a)).copy rfl (by rw [orbit_iterate_period_eq K a])).IsCycle := by
-- proof
  apply StatMech.Lattice.emb_orbit_isCycle_of_noDiagTouch K a hp h

/--
[emb_orbit_isCycle_of_kingSaturated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Wall1EmbeddingRetry.lean)
-/
@[path]
private lemma emb_orbit_isCycle_of_kingSaturated_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hp : 3 ≤ dartOrbitPeriod K a)
  (h : npm_KingSaturated K) :
-- imply
  ((dartOrbitFaceWalk K a.1 a.2 (dartOrbitPeriod K a)).copy rfl (by rw [orbit_iterate_period_eq K a])).IsCycle := by
-- proof
  apply StatMech.Lattice.emb_orbit_isCycle_of_kingSaturated K a hp h


-- created on 2026-10-23
