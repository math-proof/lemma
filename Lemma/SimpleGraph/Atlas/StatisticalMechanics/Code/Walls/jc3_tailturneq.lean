import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.jc3_tailturneq
open SimpleGraph Function StatMech StatMech.Walls


/--
[jc3_tail_turn_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_tailturneq.lean)
-/
@[path]
private lemma jc3_tail_turn_eq_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
  {a' : {e : Dart // IsBoundaryDart (K \ {r}) e}}
  {m m' n : ℕ}
-- given
  (hmatch : ∀ i, i < n → turnZ K ((dartNext K)^[m + i] a.1) = turnZ (K \ {r}) ((dartNext (K \ {r}))^[m' + i] a'.1)) :
-- imply
  jc_windowTurn K a.1 m (m + n) = jc_windowTurn (K \ {r}) a'.1 m' (m' + n) := by
-- proof
  apply StatMech.Walls.jc3_tail_turn_eq K a r a' m m' n hmatch

/--
[jc3_pendantClipMatch_tail_turn_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_tailturneq.lean)
-/
@[path]
private lemma jc3_pendantClipMatch_tail_turn_eq_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
-- given
  (h : jc2_PendantClipMatch K a r) :
-- imply
  ∃ (_ : (K \ {r}).Nonempty) (a' : {e : Dart // IsBoundaryDart (K \ {r}) e}) (m m' n : ℕ), dartOrbitPeriod K a = m + n ∧ dartOrbitPeriod (K \ {r}) a' = m' + n ∧ jc_windowTurn K a.1 m (m + n) = jc_windowTurn (K \ {r}) a'.1 m' (m' + n) := by
-- proof
  apply StatMech.Walls.jc3_pendantClipMatch_tail_turn_eq K a r h

/--
[jc3_tail_turn_eq_general](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_tailturneq.lean)
-/
@[path]
private lemma jc3_tail_turn_eq_general_eq
  {K K' : Set (Site 2)}
  {e e' : Dart}
  {m m' n : ℕ}
-- given
  (hmatch : ∀ i, i < n → turnZ K ((dartNext K)^[m + i] e) = turnZ K' ((dartNext K')^[m' + i] e')) :
-- imply
  jc_windowTurn K e m (m + n) = jc_windowTurn K' e' m' (m' + n) := by
-- proof
  apply StatMech.Walls.jc3_tail_turn_eq_general K K' e e' m m' n hmatch

/--
[jc3_tail_turn_eq_eq_engine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_tailturneq.lean)
-/
@[path]
private lemma jc3_tail_turn_eq_eq_engine_eq
  {K K' : Set (Site 2)}
  {e e' : Dart}
  {m m' n : ℕ}
-- given
  (hmatch : ∀ i, i < n → turnZ K ((dartNext K)^[m + i] e) = turnZ K' ((dartNext K')^[m' + i] e')) :
-- imply
  jc3_tail_turn_eq_general K K' e e' m m' n hmatch = jc2_tail_turn_eq K K' e e' m m' n hmatch := by
-- proof
  apply StatMech.Walls.jc3_tail_turn_eq_eq_engine K K' e e' m m' n hmatch

/--
[jc3_tail_turn_eq_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_tailturneq.lean)
-/
@[path]
private lemma jc3_tail_turn_eq_empty_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
  {a' : {e : Dart // IsBoundaryDart (K \ {r}) e}}
  {m m' : ℕ} :
-- imply
  jc_windowTurn K a.1 m (m + 0) = jc_windowTurn (K \ {r}) a'.1 m' (m' + 0) := by
-- proof
  apply StatMech.Walls.jc3_tail_turn_eq_empty K a r a' m m'

/--
[jc3_tail_turn_eq_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_tailturneq.lean)
-/
@[path]
private lemma jc3_tail_turn_eq_self_eq
  {K : Set (Site 2)}
  {e : Dart}
  {m n : ℕ} :
-- imply
  jc_windowTurn K e m (m + n) = jc_windowTurn K e m (m + n) := by
-- proof
  apply StatMech.Walls.jc3_tail_turn_eq_self K e m n


-- created on 2026-10-23
