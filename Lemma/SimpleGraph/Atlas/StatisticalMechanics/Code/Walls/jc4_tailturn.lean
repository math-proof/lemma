import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.jc4_tailturn
open SimpleGraph Function Set StatMech StatMech.Walls


/--
[jc4_tail_turn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_tailturn.lean)
-/
@[path]
private lemma jc4_tail_turn_eq
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
  apply StatMech.Walls.jc4_tail_turn K a r a' m m' n hmatch

/--
[jc4_tail_turn_of_dartLockstep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_tailturn.lean)
-/
@[path]
private lemma jc4_tail_turn_of_dartLockstep_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
  {a' : {e : Dart // IsBoundaryDart (K \ {r}) e}}
  {m m' n : ℕ}
-- given
  (htail : ∀ i, i < n → (dartNext (K \ {r}))^[m' + i] a'.1 = (dartNext K)^[m + i] a.1 ∧ bpc_NotProbed r ((dartNext K)^[m + i] a.1)) :
-- imply
  jc_windowTurn K a.1 m (m + n) = jc_windowTurn (K \ {r}) a'.1 m' (m' + n) := by
-- proof
  apply StatMech.Walls.jc4_tail_turn_of_dartLockstep K a r a' m m' n htail

/--
[jc4_orbitSpliceDatum_tail_turn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_tailturn.lean)
-/
@[path]
private lemma jc4_orbitSpliceDatum_tail_turn_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
-- given
  (h : jc3_OrbitSpliceDatum K a r) :
-- imply
  ∃ (_ : (K \ {r}).Nonempty) (a' : {e : Dart // IsBoundaryDart (K \ {r}) e}) (m m' n : ℕ), dartOrbitPeriod K a = m + n ∧ dartOrbitPeriod (K \ {r}) a' = m' + n ∧ jc_windowTurn K a.1 m (m + n) = jc_windowTurn (K \ {r}) a'.1 m' (m' + n) := by
-- proof
  apply StatMech.Walls.jc4_orbitSpliceDatum_tail_turn K a r h

/--
[jc4_tail_turn_general](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_tailturn.lean)
-/
@[path]
private lemma jc4_tail_turn_general_eq
  {K K' : Set (Site 2)}
  {e e' : Dart}
  {m m' n : ℕ}
-- given
  (hmatch : ∀ i, i < n → turnZ K ((dartNext K)^[m + i] e) = turnZ K' ((dartNext K')^[m' + i] e')) :
-- imply
  jc_windowTurn K e m (m + n) = jc_windowTurn K' e' m' (m' + n) := by
-- proof
  apply StatMech.Walls.jc4_tail_turn_general K K' e e' m m' n hmatch

/--
[jc4_tail_turn_general_eq_engine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_tailturn.lean)
-/
@[path]
private lemma jc4_tail_turn_general_eq_engine_eq
  {K K' : Set (Site 2)}
  {e e' : Dart}
  {m m' n : ℕ}
-- given
  (hmatch : ∀ i, i < n → turnZ K ((dartNext K)^[m + i] e) = turnZ K' ((dartNext K')^[m' + i] e')) :
-- imply
  jc4_tail_turn_general K K' e e' m m' n hmatch = jc2_tail_turn_eq K K' e e' m m' n hmatch := by
-- proof
  apply StatMech.Walls.jc4_tail_turn_general_eq_engine K K' e e' m m' n hmatch

/--
[jc4_tail_turn_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_tailturn.lean)
-/
@[path]
private lemma jc4_tail_turn_empty_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
  {a' : {e : Dart // IsBoundaryDart (K \ {r}) e}}
  {m m' : ℕ} :
-- imply
  jc_windowTurn K a.1 m (m + 0) = jc_windowTurn (K \ {r}) a'.1 m' (m' + 0) := by
-- proof
  apply StatMech.Walls.jc4_tail_turn_empty K a r a' m m'

/--
[jc4_tail_turn_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_tailturn.lean)
-/
@[path]
private lemma jc4_tail_turn_self_eq
  {K : Set (Site 2)}
  {e : Dart}
  {m n : ℕ} :
-- imply
  jc_windowTurn K e m (m + n) = jc_windowTurn K e m (m + n) := by
-- proof
  apply StatMech.Walls.jc4_tail_turn_self K e m n

/--
[jc4_tail_turn_of_dartLockstep_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_tailturn.lean)
-/
@[path]
private lemma jc4_tail_turn_of_dartLockstep_empty_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
  {a' : {e : Dart // IsBoundaryDart (K \ {r}) e}}
  {m m' : ℕ} :
-- imply
  jc_windowTurn K a.1 m (m + 0) = jc_windowTurn (K \ {r}) a'.1 m' (m' + 0) := by
-- proof
  apply StatMech.Walls.jc4_tail_turn_of_dartLockstep_empty K a r a' m m'


-- created on 2026-10-23
