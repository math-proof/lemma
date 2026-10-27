import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Lattice.NoPinchMatching.Part2
open SimpleGraph Function Set StatMech StatMech.Lattice


/--
[npm_kingAdj_P00_P11](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/NoPinchMatching.lean)
-/
@[path]
private lemma npm_kingAdj_P00_P11_eq
  {f : Site 2} :
-- imply
  KingAdj (npd_P00 f) (npd_P11 f) := by
-- proof
  apply StatMech.Lattice.npm_kingAdj_P00_P11 f

/--
[npm_kingAdj_P10_P01](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/NoPinchMatching.lean)
-/
@[path]
private lemma npm_kingAdj_P10_P01_eq
  {f : Site 2} :
-- imply
  KingAdj (npd_P10 f) (npd_P01 f) := by
-- proof
  apply StatMech.Lattice.npm_kingAdj_P10_P01 f

/--
[npm_diagTouch_outCorners_kingAdj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/NoPinchMatching.lean)
-/
@[path]
private lemma npm_diagTouch_outCorners_kingAdj_eq
  {K : Set (Site 2)}
  {f : Site 2}
-- given
  (h : npd_DiagTouch K f) :
-- imply
  (KingAdj (npd_P10 f) (npd_P01 f) ∧ npd_P10 f ∈ Kᶜ ∧ npd_P01 f ∈ Kᶜ) ∨ (KingAdj (npd_P00 f) (npd_P11 f) ∧ npd_P00 f ∈ Kᶜ ∧ npd_P11 f ∈ Kᶜ) := by
-- proof
  apply StatMech.Lattice.npm_diagTouch_outCorners_kingAdj h

/--
[npm_noDiagTouch_of_kingSaturated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/NoPinchMatching.lean)
-/
@[path]
private lemma npm_noDiagTouch_of_kingSaturated_eq
  {K : Set (Site 2)}
-- given
  (h : npm_KingSaturated K) :
-- imply
  npd_NoDiagTouch K := by
-- proof
  apply StatMech.Lattice.npm_noDiagTouch_of_kingSaturated h

/--
[npm_kingSaturated_diagTouch_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/NoPinchMatching.lean)
-/
@[path]
private lemma npm_kingSaturated_diagTouch_iff_eq
  {K : Set (Site 2)} :
-- imply
  npm_KingSaturated K ↔ npd_NoDiagTouch K := by
-- proof
  apply StatMech.Lattice.npm_kingSaturated_diagTouch_iff K

/--
[npm_orbitFaceNoPinch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/NoPinchMatching.lean)
-/
@[path]
private lemma npm_orbitFaceNoPinch_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (h : npm_KingSaturated K) :
-- imply
  OrbitFaceNoPinch K a := by
-- proof
  apply StatMech.Lattice.npm_orbitFaceNoPinch K a h

/--
[npm_orbitFace_injOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/NoPinchMatching.lean)
-/
@[path]
private lemma npm_orbitFace_injOn_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (h : npm_KingSaturated K) :
-- imply
  Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1)) (Set.Iio (dartOrbitPeriod K a)) := by
-- proof
  apply StatMech.Lattice.npm_orbitFace_injOn K a h

/--
[npm_diagTouch_not_kingSaturated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/NoPinchMatching.lean)
-/
@[path]
private lemma npm_diagTouch_not_kingSaturated_eq
  {K : Set (Site 2)}
  {f : Site 2}
-- given
  (h : npd_DiagTouch K f) :
-- imply
  ¬ npm_KingSaturated K := by
-- proof
  apply StatMech.Lattice.npm_diagTouch_not_kingSaturated h

/--
[npm_kingSaturated_example](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/NoPinchMatching.lean)
-/
@[path]
private lemma npm_kingSaturated_example_eq :
-- imply
  npm_KingSaturated ({![0, 0], ![1, 0], ![0, 1], ![1, 1]} : Set (Site 2)) := by
-- proof
  apply StatMech.Lattice.npm_kingSaturated_example


-- created on 2026-10-23
