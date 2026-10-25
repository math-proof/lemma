import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.kc4_eulerone.Part2
open Set SimpleGraph Function StatMech StatMech.Walls


/--
[kc4_cycleGraph_nullity_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_eulerone.lean)
-/
@[path]
private lemma kc4_cycleGraph_nullity_one_eq
  {n : ℕ} :
-- imply
  nullity (cycleGraph (n + 3)) = 1 := by
-- proof
  apply StatMech.Walls.kc4_cycleGraph_nullity_one n

/--
[kc4_cycleGraph_cyclomaticNumber_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_eulerone.lean)
-/
@[path]
private lemma kc4_cycleGraph_cyclomaticNumber_one_eq
  {n : ℕ} :
-- imply
  cyclomaticNumber (cycleGraph (n + 3)) = 1 := by
-- proof
  apply StatMech.Walls.kc4_cycleGraph_cyclomaticNumber_one n

/--
[kc4_cycleGraph_boundedFaceCount_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_eulerone.lean)
-/
@[path]
private lemma kc4_cycleGraph_boundedFaceCount_two_eq
  {n : ℕ} :
-- imply
  faceCount (cycleGraph (n + 3)) = 2 := by
-- proof
  apply StatMech.Walls.kc4_cycleGraph_boundedFaceCount_two n

/--
[kc4_eulerOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_eulerone.lean)
-/
@[path]
private lemma kc4_eulerOne_eq
  {p : ℕ}
-- given
  (hp : 3 ≤ p) :
-- imply
  kc4_contourEulerChar p = 1 := by
-- proof
  apply StatMech.Walls.kc4_eulerOne hp

/--
[kc4_eulerOne_cycleGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_eulerone.lean)
-/
@[path]
private lemma kc4_eulerOne_cycleGraph_eq
  {n : ℕ} :
-- imply
  kc4_contourEulerChar (n + 3) = cyclomaticNumber (cycleGraph (n + 3)) := by
-- proof
  apply StatMech.Walls.kc4_eulerOne_cycleGraph n

/--
[kc4_orbitLoop_nullity_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_eulerone.lean)
-/
@[path]
private lemma kc4_orbitLoop_nullity_one_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hp : 3 ≤ dartOrbitPeriod K a)
  (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1)) (Set.Iio (dartOrbitPeriod K a))) :
-- imply
  nullity (mpl_orbitLoop K a).toSubgraph.coe = 1 := by
-- proof
  apply StatMech.Walls.kc4_orbitLoop_nullity_one K a hp hinj

/--
[kc4_orbitLoop_boundedFaceCount_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_eulerone.lean)
-/
@[path]
private lemma kc4_orbitLoop_boundedFaceCount_two_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hp : 3 ≤ dartOrbitPeriod K a)
  (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1)) (Set.Iio (dartOrbitPeriod K a))) :
-- imply
  faceCount (mpl_orbitLoop K a).toSubgraph.coe = 2 := by
-- proof
  apply StatMech.Walls.kc4_orbitLoop_boundedFaceCount_two K a hp hinj

/--
[kc4_box_orbitLoop_nullity_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_eulerone.lean)
-/
@[path]
private lemma kc4_box_orbitLoop_nullity_one_eq
  {n : ℕ}
  {a : {e : Dart // IsBoundaryDart (box 2 n) e}}
-- given
  (hp : 3 ≤ dartOrbitPeriod (box 2 n) a) :
-- imply
  nullity (((dartOrbitFaceWalk (box 2 n) a.1 a.2 (dartOrbitPeriod (box 2 n) a)).copy rfl (by rw [orbit_iterate_period_eq (box 2 n) a]))).toSubgraph.coe = 1 := by
-- proof
  apply StatMech.Walls.kc4_box_orbitLoop_nullity_one n a hp

/--
[kc4_box_orbitLoop_boundedFaceCount_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_eulerone.lean)
-/
@[path]
private lemma kc4_box_orbitLoop_boundedFaceCount_two_eq
  {n : ℕ}
  {a : {e : Dart // IsBoundaryDart (box 2 n) e}}
-- given
  (hp : 3 ≤ dartOrbitPeriod (box 2 n) a) :
-- imply
  faceCount (((dartOrbitFaceWalk (box 2 n) a.1 a.2 (dartOrbitPeriod (box 2 n) a)).copy rfl (by rw [orbit_iterate_period_eq (box 2 n) a]))).toSubgraph.coe = 2 := by
-- proof
  apply StatMech.Walls.kc4_box_orbitLoop_boundedFaceCount_two n a hp

/--
[kc4_contourEulerChar_eq_jwd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_eulerone.lean)
-/
@[path]
private lemma kc4_contourEulerChar_eq_jwd_eq
  {p : ℕ} :
-- imply
  kc4_contourEulerChar p = contourEulerChar p := by
-- proof
  apply StatMech.Walls.kc4_contourEulerChar_eq_jwd p

/--
[kc4_eulerOne_eq_jwd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_eulerone.lean)
-/
@[path]
private lemma kc4_eulerOne_eq_jwd_eq
  {p : ℕ}
-- given
  (hp : 3 ≤ p) :
-- imply
  kc4_contourEulerChar p = contourEulerChar p ∧ kc4_contourEulerChar p = 1 := by
-- proof
  apply StatMech.Walls.kc4_eulerOne_eq_jwd hp


-- created on 2026-10-23
