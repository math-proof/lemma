import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.jwd_singletonturnfour
open SimpleGraph Function StatMech StatMech.Walls


/--
[jwd_singleton_totalTurn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_singletonturnfour.lean)
-/
@[path]
private lemma jwd_singleton_totalTurn_eq
  {v : Site 2}
  {a : {e : Dart // IsBoundaryDart ({v} : Set (Site 2)) e}} :
-- imply
  totalTurnZ ({v} : Set (Site 2)) a.1 (dartOrbitPeriod ({v} : Set (Site 2)) a) = -4 := by
-- proof
  apply StatMech.Walls.jwd_singleton_totalTurn v a

/--
[jwd_singleton_cornerBalance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_singletonturnfour.lean)
-/
@[path]
private lemma jwd_singleton_cornerBalance_eq
  {v : Site 2}
  {a : {e : Dart // IsBoundaryDart ({v} : Set (Site 2)) e}} :
-- imply
  cornerBalance ({v} : Set (Site 2)) a = -4 := by
-- proof
  apply StatMech.Walls.jwd_singleton_cornerBalance v a

/--
[jwd_singleton_corner_counts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_singletonturnfour.lean)
-/
@[path]
private lemma jwd_singleton_corner_counts_eq
  {v : Site 2}
  {a : {e : Dart // IsBoundaryDart ({v} : Set (Site 2)) e}} :
-- imply
  rightCornerCount ({v} : Set (Site 2)) a.1 (dartOrbitPeriod ({v} : Set (Site 2)) a) - leftCornerCount ({v} : Set (Site 2)) a.1 (dartOrbitPeriod ({v} : Set (Site 2)) a) = -4 := by
-- proof
  apply StatMech.Walls.jwd_singleton_corner_counts v a

/--
[jwd_singleton_eq_transUnitCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_singletonturnfour.lean)
-/
@[path]
private lemma jwd_singleton_eq_transUnitCell_eq
  {v : Site 2} :
-- imply
  ({v} : Set (Site 2)) = transSet v unitCell := by
-- proof
  apply StatMech.Walls.jwd_singleton_eq_transUnitCell v

/--
[jwd_singleton_totalTurn_reduce](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_singletonturnfour.lean)
-/
@[path]
private lemma jwd_singleton_totalTurn_reduce_eq
  {v : Site 2}
  {a : {e : Dart // IsBoundaryDart ({v} : Set (Site 2)) e}}
  {b : {e : Dart // IsBoundaryDart unitCell e}}
-- given
  (he : a.1 = transDart v b.1) :
-- imply
  totalTurnZ ({v} : Set (Site 2)) a.1 (dartOrbitPeriod ({v} : Set (Site 2)) a) = totalTurnZ unitCell b.1 (dartOrbitPeriod unitCell b) := by
-- proof
  apply StatMech.Walls.jwd_singleton_totalTurn_reduce v a b he

/--
[jwd_unitCell_totalTurn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_singletonturnfour.lean)
-/
@[path]
private lemma jwd_unitCell_totalTurn_eq
  {a : {e : Dart // IsBoundaryDart unitCell e}}
-- given
  (ha : a.1 = ucDart0 ∨ a.1 = ucDart1 ∨ a.1 = ucDart2 ∨ a.1 = ucDart3) :
-- imply
  totalTurnZ unitCell a.1 (dartOrbitPeriod unitCell a) = -4 := by
-- proof
  apply StatMech.Walls.jwd_unitCell_totalTurn a ha

/--
[jwd_singleton_turningIsFullRevolution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_singletonturnfour.lean)
-/
@[path]
private lemma jwd_singleton_turningIsFullRevolution_eq
  {v : Site 2}
  {a : {e : Dart // IsBoundaryDart ({v} : Set (Site 2)) e}} :
-- imply
  TurningIsFullRevolution ({v} : Set (Site 2)) a := by
-- proof
  apply StatMech.Walls.jwd_singleton_turningIsFullRevolution v a

/--
[jwd_singleton_orbitPeriod_ge_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_singletonturnfour.lean)
-/
@[path]
private lemma jwd_singleton_orbitPeriod_ge_four_eq
  {v : Site 2}
  {a : {e : Dart // IsBoundaryDart ({v} : Set (Site 2)) e}} :
-- imply
  4 ≤ dartOrbitPeriod ({v} : Set (Site 2)) a := by
-- proof
  apply StatMech.Walls.jwd_singleton_orbitPeriod_ge_four v a


-- created on 2026-10-23
