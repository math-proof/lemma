import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.jc10cornerexists
open SimpleGraph Function Set StatMech StatMech.Walls


/--
[jc10_extremeCell_leftDart_convex_corner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc10cornerexists.lean)
-/
@[path]
private lemma jc10_extremeCell_leftDart_convex_corner_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (hc : IsExtremeCell K c) :
-- imply
  IsBoundaryDart K (leftDart c) ∧ turnZ K (leftDart c) = -1 := by
-- proof
  apply StatMech.Walls.jc10_extremeCell_leftDart_convex_corner K c hc

/--
[jc10_exists_extremeCell_convex_corner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc10cornerexists.lean)
-/
@[path]
private lemma jc10_exists_extremeCell_convex_corner_eq
  {K : Set (Site 2)}
-- given
  (hK : K.Finite)
  (hne : K.Nonempty) :
-- imply
  ∃ c : Site 2, IsExtremeCell K c ∧ IsBoundaryDart K (leftDart c) ∧ turnZ K (leftDart c) = -1 := by
-- proof
  apply StatMech.Walls.jc10_exists_extremeCell_convex_corner K hK hne

/--
[jc10_corner_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc10cornerexists.lean)
-/
@[path]
private lemma jc10_corner_exists_eq
  {K : Set (Site 2)}
-- given
  (hK : K.Finite)
  (hne : K.Nonempty) :
-- imply
  ∃ e : Dart, IsBoundaryDart K e ∧ turnZ K e = -1 := by
-- proof
  apply StatMech.Walls.jc10_corner_exists K hK hne

/--
[jc10_nonempty_of_boundaryDart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc10cornerexists.lean)
-/
@[path]
private lemma jc10_nonempty_of_boundaryDart_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (he : IsBoundaryDart K e) :
-- imply
  K.Nonempty := by
-- proof
  apply StatMech.Walls.jc10_nonempty_of_boundaryDart K e he

/--
[jc10_corner_exists_iff_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc10cornerexists.lean)
-/
@[path]
private lemma jc10_corner_exists_iff_nonempty_eq
  {K : Set (Site 2)}
-- given
  (hK : K.Finite) :
-- imply
  (∃ e : Dart, IsBoundaryDart K e ∧ turnZ K e = -1) ↔ K.Nonempty := by
-- proof
  apply StatMech.Walls.jc10_corner_exists_iff_nonempty K hK


-- created on 2026-10-23
