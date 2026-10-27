import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.jwd_earexists
open SimpleGraph Function StatMech StatMech.Walls


/--
[jwd_extremeCell_isEar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_earexists.lean)
-/
@[path]
private lemma jwd_extremeCell_isEar_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (hc : IsExtremeCell K c) :
-- imply
  jwd_ExtremeEar K c where isExtreme := by
-- proof
  apply StatMech.Walls.jwd_extremeCell_isEar K c hc

/--
[jwd_earExists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_earexists.lean)
-/
@[path]
private lemma jwd_earExists_eq
  {K : Set (Site 2)}
-- given
  (hK : K.Finite)
  (hne : K.Nonempty) :
-- imply
  ∃ c, jwd_ExtremeEar K c := by
-- proof
  apply StatMech.Walls.jwd_earExists K hK hne

/--
[jwd_exists_convex_corner_dart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_earexists.lean)
-/
@[path]
private lemma jwd_exists_convex_corner_dart_eq
  {K : Set (Site 2)}
-- given
  (hK : K.Finite)
  (hne : K.Nonempty) :
-- imply
  ∃ e : Dart, IsBoundaryDart K e ∧ turnZ K e = -1 := by
-- proof
  apply StatMech.Walls.jwd_exists_convex_corner_dart K hK hne

/--
[jwd_earExists_explicit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_earexists.lean)
-/
@[path]
private lemma jwd_earExists_explicit_eq
  {K : Set (Site 2)}
-- given
  (hK : K.Finite)
  (hne : K.Nonempty) :
-- imply
  ∃ c, c ∈ K ∧ IsBoundaryDart K (leftDart c) ∧ turnZ K (leftDart c) = -1 ∧ (∀ v ∈ K, lexKey v ≤ lexKey c) := by
-- proof
  apply StatMech.Walls.jwd_earExists_explicit K hK hne

/--
[jwd_unitCell_earExists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_earexists.lean)
-/
@[path]
private lemma jwd_unitCell_earExists_eq :
-- imply
  ∃ c, jwd_ExtremeEar unitCell c := by
-- proof
  apply StatMech.Walls.jwd_unitCell_earExists


-- created on 2026-10-23
