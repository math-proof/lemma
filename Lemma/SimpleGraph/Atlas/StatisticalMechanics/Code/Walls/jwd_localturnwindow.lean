import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.jwd_localturnwindow
open SimpleGraph Function Set Finset StatMech StatMech.Walls


/--
[jwd_untouched_localTurn_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_localturnwindow.lean)
-/
@[path]
private lemma jwd_untouched_localTurn_zero_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {f : Site 2}
-- given
  (h : usc_visitSet K a f = ∅) :
-- imply
  usc_localTurn K a f = 0 := by
-- proof
  apply StatMech.Walls.jwd_untouched_localTurn_zero K a f h

/--
[jwd_touched_localTurn_eq_lone_turnZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_localturnwindow.lean)
-/
@[path]
private lemma jwd_touched_localTurn_eq_lone_turnZ_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {f : Site 2}
-- given
  (hmult : usc_FaceMultiplicityOne K a)
  (hne : (usc_visitSet K a f).Nonempty) :
-- imply
  ∃ i, usc_visitSet K a f = {i} ∧ usc_localTurn K a f = turnZ K ((dartNext K)^[i] a.1) := by
-- proof
  apply StatMech.Walls.jwd_touched_localTurn_eq_lone_turnZ K a hmult f hne

/--
[jwd_turnZ_window](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_localturnwindow.lean)
-/
@[path]
private lemma jwd_turnZ_window_eq
  {K : Set (Site 2)}
  {e : Dart} :
-- imply
  turnZ K e = 1 ∨ turnZ K e = 0 ∨ turnZ K e = -1 := by
-- proof
  apply StatMech.Walls.jwd_turnZ_window K e

/--
[jwd_localTurn_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_localturnwindow.lean)
-/
@[path]
private lemma jwd_localTurn_mem_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {f : Site 2}
-- given
  (hmult : usc_FaceMultiplicityOne K a) :
-- imply
  usc_localTurn K a f = 1 ∨ usc_localTurn K a f = 0 ∨ usc_localTurn K a f = -1 := by
-- proof
  apply StatMech.Walls.jwd_localTurn_mem K a hmult f

/--
[jwd_starHull_touched_localTurn_eq_lone_turnZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_localturnwindow.lean)
-/
@[path]
private lemma jwd_starHull_touched_localTurn_eq_lone_turnZ_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
  {f : Site 2}
-- given
  (hne : (usc_visitSet (ndt_StarHull K) a f).Nonempty) :
-- imply
  ∃ i, usc_visitSet (ndt_StarHull K) a f = {i} ∧ usc_localTurn (ndt_StarHull K) a f = turnZ (ndt_StarHull K) ((dartNext (ndt_StarHull K))^[i] a.1) := by
-- proof
  apply StatMech.Walls.jwd_starHull_touched_localTurn_eq_lone_turnZ K a f hne

/--
[jwd_starHull_localTurn_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_localturnwindow.lean)
-/
@[path]
private lemma jwd_starHull_localTurn_mem_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
  {f : Site 2} :
-- imply
  usc_localTurn (ndt_StarHull K) a f = 1 ∨ usc_localTurn (ndt_StarHull K) a f = 0 ∨ usc_localTurn (ndt_StarHull K) a f = -1 := by
-- proof
  apply StatMech.Walls.jwd_starHull_localTurn_mem K a f


-- created on 2026-10-23
