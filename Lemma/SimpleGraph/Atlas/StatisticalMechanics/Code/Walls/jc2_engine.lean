import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.jc2_engine
open SimpleGraph Function StatMech StatMech.Walls


/--
[jc2_windowTurn_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_engine.lean)
-/
@[path]
private lemma jc2_windowTurn_eq_eq
  {K : Set (Site 2)}
  {e : Dart}
  {a b : ℕ} :
-- imply
  jc_windowTurn K e a b = umEar_windowTurn K e a b := by
-- proof
  apply StatMech.Walls.jc2_windowTurn_eq K e a b

/--
[jc2_totalTurnZ_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_engine.lean)
-/
@[path]
private lemma jc2_totalTurnZ_split_eq
  {K : Set (Site 2)}
  {e : Dart}
  {m p : ℕ}
-- given
  (hm : m ≤ p) :
-- imply
  totalTurnZ K e p = jc_windowTurn K e 0 m + jc_windowTurn K e m p := by
-- proof
  apply StatMech.Walls.jc2_totalTurnZ_split K e m p hm

/--
[jc2_tail_turn_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_engine.lean)
-/
@[path]
private lemma jc2_tail_turn_eq_eq
  {K K' : Set (Site 2)}
  {e e' : Dart}
  {m m' n : ℕ}
-- given
  (hmatch : ∀ i, i < n → turnZ K ((dartNext K)^[m + i] e) = turnZ K' ((dartNext K')^[m' + i] e')) :
-- imply
  jc_windowTurn K e m (m + n) = jc_windowTurn K' e' m' (m' + n) := by
-- proof
  apply StatMech.Walls.jc2_tail_turn_eq K K' e e' m m' n hmatch

/--
[jc2_contraction_turning_change](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_engine.lean)
-/
@[path]
private lemma jc2_contraction_turning_change_eq
  {K K' : Set (Site 2)}
  {e e' : Dart}
  {m m' n : ℕ}
-- given
  (hmatch : ∀ i, i < n → turnZ K ((dartNext K)^[m + i] e) = turnZ K' ((dartNext K')^[m' + i] e')) :
-- imply
  totalTurnZ K' e' (m' + n) = totalTurnZ K e (m + n) + (jc_windowTurn K' e' 0 m' - jc_windowTurn K e 0 m) := by
-- proof
  apply StatMech.Walls.jc2_contraction_turning_change K K' e e' m m' n hmatch

/--
[jc2_engine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_engine.lean)
-/
@[path]
private lemma jc2_engine_eq
  {K K' : Set (Site 2)}
  {e e' : Dart}
  {m m' n : ℕ}
-- given
  (hmatch : ∀ i, i < n → turnZ K ((dartNext K)^[m + i] e) = turnZ K' ((dartNext K')^[m' + i] e'))
  (hbal : jc_windowTurn K' e' 0 m' = jc_windowTurn K e 0 m) :
-- imply
  totalTurnZ K' e' (m' + n) = totalTurnZ K e (m + n) := by
-- proof
  apply StatMech.Walls.jc2_engine K K' e e' m m' n hmatch hbal

/--
[jc2_engine_period](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_engine.lean)
-/
@[path]
private lemma jc2_engine_period_eq
  {K K' : Set (Site 2)}
  {e e' : Dart}
  {m m' n p p' : ℕ}
-- given
  (hp : p = m + n)
  (hp' : p' = m' + n)
  (hmatch : ∀ i, i < n → turnZ K ((dartNext K)^[m + i] e) = turnZ K' ((dartNext K')^[m' + i] e'))
  (hbal : jc_windowTurn K' e' 0 m' = jc_windowTurn K e 0 m) :
-- imply
  totalTurnZ K' e' p' = totalTurnZ K e p := by
-- proof
  apply StatMech.Walls.jc2_engine_period K K' e e' m m' n p p' hp hp' hmatch hbal

/--
[jc2_engine_balance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_engine.lean)
-/
@[path]
private lemma jc2_engine_balance_eq
  {K K' : Set (Site 2)}
  {e e' : Dart}
  {m m' n : ℕ}
-- given
  (hmatch : ∀ i, i < n → turnZ K ((dartNext K)^[m + i] e) = turnZ K' ((dartNext K')^[m' + i] e'))
  (hbal : umEar_windowRight K' e' 0 m' - umEar_windowLeft K' e' 0 m' = umEar_windowRight K e 0 m - umEar_windowLeft K e 0 m) :
-- imply
  totalTurnZ K' e' (m' + n) = totalTurnZ K e (m + n) := by
-- proof
  apply StatMech.Walls.jc2_engine_balance K K' e e' m m' n hmatch hbal

/--
[jc2_engine_eq_turnPreserveEngine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_engine.lean)
-/
@[path]
private lemma jc2_engine_eq_turnPreserveEngine_eq
  {K K' : Set (Site 2)}
  {e e' : Dart}
  {m m' n : ℕ}
-- given
  (hmatch : ∀ i, i < n → turnZ K ((dartNext K)^[m + i] e) = turnZ K' ((dartNext K')^[m' + i] e'))
  (hbal : jc_windowTurn K' e' 0 m' = jc_windowTurn K e 0 m) :
-- imply
  jc2_engine K K' e e' m m' n hmatch hbal = jc_ear_step_preserves_turn K K' e e' m m' n hmatch hbal := by
-- proof
  apply StatMech.Walls.jc2_engine_eq_turnPreserveEngine K K' e e' m m' n hmatch hbal

/--
[jc2_engine_saturating_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_engine.lean)
-/
@[path]
private lemma jc2_engine_saturating_pos_eq
  {K K' : Set (Site 2)}
  {e e' : Dart}
  {m m' n : ℕ}
-- given
  (hmatch : ∀ i, i < n → turnZ K ((dartNext K)^[m + i] e) = turnZ K' ((dartNext K')^[m' + i] e'))
  (hbal : jc_windowTurn K' e' 0 m' = jc_windowTurn K e 0 m)
  (hval : totalTurnZ K e (m + n) = 4) :
-- imply
  totalTurnZ K' e' (m' + n) = 4 := by
-- proof
  apply StatMech.Walls.jc2_engine_saturating_pos K K' e e' m m' n hmatch hbal hval

/--
[jc2_engine_saturating_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_engine.lean)
-/
@[path]
private lemma jc2_engine_saturating_neg_eq
  {K K' : Set (Site 2)}
  {e e' : Dart}
  {m m' n : ℕ}
-- given
  (hmatch : ∀ i, i < n → turnZ K ((dartNext K)^[m + i] e) = turnZ K' ((dartNext K')^[m' + i] e'))
  (hbal : jc_windowTurn K' e' 0 m' = jc_windowTurn K e 0 m)
  (hval : totalTurnZ K e (m + n) = -4) :
-- imply
  totalTurnZ K' e' (m' + n) = -4 := by
-- proof
  apply StatMech.Walls.jc2_engine_saturating_neg K K' e e' m m' n hmatch hbal hval

/--
[jc2_engine_saturating_full_revolution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_engine.lean)
-/
@[path]
private lemma jc2_engine_saturating_full_revolution_eq
  {K K' : Set (Site 2)}
  {e e' : Dart}
  {m m' n : ℕ}
-- given
  (hmatch : ∀ i, i < n → turnZ K ((dartNext K)^[m + i] e) = turnZ K' ((dartNext K')^[m' + i] e'))
  (hbal : jc_windowTurn K' e' 0 m' = jc_windowTurn K e 0 m)
  (hval : totalTurnZ K e (m + n) = 4 ∨ totalTurnZ K e (m + n) = -4) :
-- imply
  totalTurnZ K' e' (m' + n) = 4 ∨ totalTurnZ K' e' (m' + n) = -4 := by
-- proof
  apply StatMech.Walls.jc2_engine_saturating_full_revolution K K' e e' m m' n hmatch hbal hval

/--
[jc2_domino_contracts_to_unitCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_engine.lean)
-/
@[path]
private lemma jc2_domino_contracts_to_unitCell_eq :
-- imply
  totalTurnZ unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) = totalTurnZ domino dmBase.1 (dartOrbitPeriod domino dmBase) := by
-- proof
  apply StatMech.Walls.jc2_domino_contracts_to_unitCell

/--
[jc2_domino_unitCell_saturating_value](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_engine.lean)
-/
@[path]
private lemma jc2_domino_unitCell_saturating_value_eq :
-- imply
  totalTurnZ domino dmD0 6 = -4 ∧ totalTurnZ unitCell ucDart0 4 = -4 := by
-- proof
  apply StatMech.Walls.jc2_domino_unitCell_saturating_value


-- created on 2026-10-23
