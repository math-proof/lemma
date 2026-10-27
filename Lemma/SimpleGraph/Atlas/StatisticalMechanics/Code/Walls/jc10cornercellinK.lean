import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.jc10cornercellinK
open SimpleGraph Function Set StatMech StatMech.Walls


/--
[jc10_cornerInsideCell_def](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc10cornercellinK.lean)
-/
@[path]
private lemma jc10_cornerInsideCell_def_eq
  {e : Dart} :
-- imply
  jc10_cornerInsideCell e = e.tail := by
-- proof
  apply StatMech.Walls.jc10_cornerInsideCell_def e

/--
[jc10_cornerInsideCell_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc10cornercellinK.lean)
-/
@[path]
private lemma jc10_cornerInsideCell_mem_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (he : IsBoundaryDart K e) :
-- imply
  jc10_cornerInsideCell e ∈ K := by
-- proof
  apply StatMech.Walls.jc10_cornerInsideCell_mem K e he

/--
[jc10_convexCorner_front_nmem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc10cornercellinK.lean)
-/
@[path]
private lemma jc10_convexCorner_front_nmem_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (h : turnZ K e = -1) :
-- imply
  e.head + (-rot90Fun e.dir) ∉ K := by
-- proof
  apply StatMech.Walls.jc10_convexCorner_front_nmem K e h

/--
[jc10_convexCorner_side_nmem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc10cornercellinK.lean)
-/
@[path]
private lemma jc10_convexCorner_side_nmem_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (h : turnZ K e = -1) :
-- imply
  e.tail + (-rot90Fun e.dir) ∉ K := by
-- proof
  apply StatMech.Walls.jc10_convexCorner_side_nmem K e h

/--
[jc10_convexCorner_unique_insideCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc10cornercellinK.lean)
-/
@[path]
private lemma jc10_convexCorner_unique_insideCell_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (he : IsBoundaryDart K e)
  (hturn : turnZ K e = -1) :
-- imply
  jc10_cornerInsideCell e ∈ K ∧ e.head + (-rot90Fun e.dir) ∉ K ∧ e.tail + (-rot90Fun e.dir) ∉ K := by
-- proof
  apply StatMech.Walls.jc10_convexCorner_unique_insideCell K e he hturn

/--
[jc10_exists_convex_corner_insideCell_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc10cornercellinK.lean)
-/
@[path]
private lemma jc10_exists_convex_corner_insideCell_mem_eq
  {K : Set (Site 2)}
-- given
  (hK : K.Finite)
  (hne : K.Nonempty) :
-- imply
  ∃ e : Dart, IsBoundaryDart K e ∧ turnZ K e = -1 ∧ jc10_cornerInsideCell e ∈ K ∧ e.head + (-rot90Fun e.dir) ∉ K ∧ e.tail + (-rot90Fun e.dir) ∉ K := by
-- proof
  apply StatMech.Walls.jc10_exists_convex_corner_insideCell_mem K hK hne

/--
[jc10_extremeCell_insideCell_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc10cornercellinK.lean)
-/
@[path]
private lemma jc10_extremeCell_insideCell_eq_eq
  {c : Site 2} :
-- imply
  jc10_cornerInsideCell (leftDart c) = c := by
-- proof
  apply StatMech.Walls.jc10_extremeCell_insideCell_eq c

/--
[jc10_extremeCell_insideCell_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc10cornercellinK.lean)
-/
@[path]
private lemma jc10_extremeCell_insideCell_mem_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (hc : IsExtremeCell K c) :
-- imply
  jc10_cornerInsideCell (leftDart c) ∈ K := by
-- proof
  apply StatMech.Walls.jc10_extremeCell_insideCell_mem K c hc

/--
[jc10_unitCell_insideCell_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc10cornercellinK.lean)
-/
@[path]
private lemma jc10_unitCell_insideCell_mem_eq :
-- imply
  jc10_cornerInsideCell ucDart0 ∈ unitCell := by
-- proof
  apply StatMech.Walls.jc10_unitCell_insideCell_mem

/--
[jc10_unitCell_convexCorner_unique_insideCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc10cornercellinK.lean)
-/
@[path]
private lemma jc10_unitCell_convexCorner_unique_insideCell_eq :
-- imply
  jc10_cornerInsideCell ucDart0 ∈ unitCell ∧ ucDart0.head + (-rot90Fun ucDart0.dir) ∉ unitCell ∧ ucDart0.tail + (-rot90Fun ucDart0.dir) ∉ unitCell := by
-- proof
  apply StatMech.Walls.jc10_unitCell_convexCorner_unique_insideCell


-- created on 2026-10-23
