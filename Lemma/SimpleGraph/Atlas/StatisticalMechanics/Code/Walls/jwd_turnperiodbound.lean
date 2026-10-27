import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.jwd_turnperiodbound
open SimpleGraph Function StatMech StatMech.Walls


/--
[jwd_step_turn_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_turnperiodbound.lean)
-/
@[path]
private lemma jwd_step_turn_le_one_eq
  {K : Set (Site 2)}
  {e : Dart} :
-- imply
  |turnZ K e| ≤ 1 := by
-- proof
  apply StatMech.Walls.jwd_step_turn_le_one K e

/--
[jwd_step_turn_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_turnperiodbound.lean)
-/
@[path]
private lemma jwd_step_turn_mem_eq
  {K : Set (Site 2)}
  {e : Dart} :
-- imply
  turnZ K e = 1 ∨ turnZ K e = 0 ∨ turnZ K e = -1 := by
-- proof
  apply StatMech.Walls.jwd_step_turn_mem K e

/--
[jwd_totalTurn_le_steps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_turnperiodbound.lean)
-/
@[path]
private lemma jwd_totalTurn_le_steps_eq
  {K : Set (Site 2)}
  {e : Dart}
  {p : ℕ} :
-- imply
  |totalTurnZ K e p| ≤ (p : ℤ) := by
-- proof
  apply StatMech.Walls.jwd_totalTurn_le_steps K e p

/--
[jwd_turn_period_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_turnperiodbound.lean)
-/
@[path]
private lemma jwd_turn_period_bound_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  |totalTurnZ K a.1 (dartOrbitPeriod K a)| ≤ (dartOrbitPeriod K a : ℤ) := by
-- proof
  apply StatMech.Walls.jwd_turn_period_bound K a

/--
[jwd_turn_period_bound_explicit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_turnperiodbound.lean)
-/
@[path]
private lemma jwd_turn_period_bound_explicit_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  |totalTurnZ K a.1 (dartOrbitPeriod K a)| ≤ (dartOrbitPeriod K a : ℤ) := by
-- proof
  apply StatMech.Walls.jwd_turn_period_bound_explicit K a

/--
[jwd_turn_bracketed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_turnperiodbound.lean)
-/
@[path]
private lemma jwd_turn_bracketed_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  (4 : ℤ) ∣ totalTurnZ K a.1 (dartOrbitPeriod K a) ∧ |totalTurnZ K a.1 (dartOrbitPeriod K a)| ≤ (dartOrbitPeriod K a : ℤ) := by
-- proof
  apply StatMech.Walls.jwd_turn_bracketed K a


-- created on 2026-10-23
