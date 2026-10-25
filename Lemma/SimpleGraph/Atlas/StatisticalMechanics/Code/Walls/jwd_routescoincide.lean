import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.jwd_routescoincide
open SimpleGraph Function StatMech StatMech.Walls


/--
[cornerBalance_eq_four_revCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_routescoincide.lean)
-/
@[path]
private lemma cornerBalance_eq_four_revCount_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  cornerBalance K a = 4 * revCount K a := by
-- proof
  apply StatMech.Walls.cornerBalance_eq_four_revCount K a

/--
[cornerBalance_eq_four_iff_revCount_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_routescoincide.lean)
-/
@[path]
private lemma cornerBalance_eq_four_iff_revCount_eq_one_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  (cornerBalance K a = 4 ∨ cornerBalance K a = -4) ↔ (revCount K a = 1 ∨ revCount K a = -1) := by
-- proof
  apply StatMech.Walls.cornerBalance_eq_four_iff_revCount_eq_one K a

/--
[eulerCharOne_iff_revCount_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_routescoincide.lean)
-/
@[path]
private lemma eulerCharOne_iff_revCount_eq_one_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hp : 3 ≤ dartOrbitPeriod K a) :
-- imply
  EulerCharOne K a ↔ (revCount K a = 1 ∨ revCount K a = -1) := by
-- proof
  apply StatMech.Walls.eulerCharOne_iff_revCount_eq_one K a hp

/--
[routes_coincide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_routescoincide.lean)
-/
@[path]
private lemma routes_coincide_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hp : 3 ≤ dartOrbitPeriod K a) :
-- imply
  ((cornerBalance K a = 4 ∨ cornerBalance K a = -4) ↔ (revCount K a = 1 ∨ revCount K a = -1)) ∧ (EulerCharOne K a ↔ (revCount K a = 1 ∨ revCount K a = -1)) ∧ (TurningIsFullRevolution K a ↔ (revCount K a = 1 ∨ revCount K a = -1)) := by
-- proof
  apply StatMech.Walls.routes_coincide K a hp

/--
[cornerBalance_eq_four_iff_turningIsFullRevolution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_routescoincide.lean)
-/
@[path]
private lemma cornerBalance_eq_four_iff_turningIsFullRevolution_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  (cornerBalance K a = 4 ∨ cornerBalance K a = -4) ↔ TurningIsFullRevolution K a := by
-- proof
  apply StatMech.Walls.cornerBalance_eq_four_iff_turningIsFullRevolution K a

/--
[eulerCharOne_iff_cornerBalance_eq_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_routescoincide.lean)
-/
@[path]
private lemma eulerCharOne_iff_cornerBalance_eq_four_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hp : 3 ≤ dartOrbitPeriod K a) :
-- imply
  EulerCharOne K a ↔ (cornerBalance K a = 4 ∨ cornerBalance K a = -4) := by
-- proof
  apply StatMech.Walls.eulerCharOne_iff_cornerBalance_eq_four K a hp

/--
[unitCell_revCount_eq_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_routescoincide.lean)
-/
@[path]
private lemma unitCell_revCount_eq_neg_one_eq :
-- imply
  revCount unitCell ucBase = -1 := by
-- proof
  apply StatMech.Walls.unitCell_revCount_eq_neg_one

/--
[domino_cornerBalance_eq_neg_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_routescoincide.lean)
-/
@[path]
private lemma domino_cornerBalance_eq_neg_four_eq :
-- imply
  cornerBalance domino dmBase = -4 := by
-- proof
  apply StatMech.Walls.domino_cornerBalance_eq_neg_four

/--
[domino_revCount_eq_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_routescoincide.lean)
-/
@[path]
private lemma domino_revCount_eq_neg_one_eq :
-- imply
  revCount domino dmBase = -1 := by
-- proof
  apply StatMech.Walls.domino_revCount_eq_neg_one

/--
[unitCell_routes_coincide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_routescoincide.lean)
-/
@[path]
private lemma unitCell_routes_coincide_eq :
-- imply
  ((cornerBalance unitCell ucBase = 4 ∨ cornerBalance unitCell ucBase = -4) ↔ (revCount unitCell ucBase = 1 ∨ revCount unitCell ucBase = -1)) ∧ (EulerCharOne unitCell ucBase ↔ (revCount unitCell ucBase = 1 ∨ revCount unitCell ucBase = -1)) ∧ (TurningIsFullRevolution unitCell ucBase ↔ (revCount unitCell ucBase = 1 ∨ revCount unitCell ucBase = -1)) := by
-- proof
  apply StatMech.Walls.unitCell_routes_coincide

/--
[domino_routes_coincide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_routescoincide.lean)
-/
@[path]
private lemma domino_routes_coincide_eq :
-- imply
  ((cornerBalance domino dmBase = 4 ∨ cornerBalance domino dmBase = -4) ↔ (revCount domino dmBase = 1 ∨ revCount domino dmBase = -1)) ∧ (EulerCharOne domino dmBase ↔ (revCount domino dmBase = 1 ∨ revCount domino dmBase = -1)) ∧ (TurningIsFullRevolution domino dmBase ↔ (revCount domino dmBase = 1 ∨ revCount domino dmBase = -1)) := by
-- proof
  apply StatMech.Walls.domino_routes_coincide


-- created on 2026-10-23
