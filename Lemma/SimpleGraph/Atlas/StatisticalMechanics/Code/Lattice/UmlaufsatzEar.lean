import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.UmlaufsatzEar.Part2
open SimpleGraph Function StatMech StatMech.Lattice


/--
[umEar_windowTurn_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzEar.lean)
-/
@[path]
private lemma umEar_windowTurn_self_eq
  {K : Set (Site 2)}
  {e : Dart}
  {a : ℕ} :
-- imply
  umEar_windowTurn K e a a = 0 := by
-- proof
  apply StatMech.Lattice.umEar_windowTurn_self K e a

/--
[umEar_windowTurn_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzEar.lean)
-/
@[path]
private lemma umEar_windowTurn_add_eq
  {K : Set (Site 2)}
  {e : Dart}
  {a b c : ℕ}
-- given
  (hab : a ≤ b)
  (hbc : b ≤ c) :
-- imply
  umEar_windowTurn K e a c = umEar_windowTurn K e a b + umEar_windowTurn K e b c := by
-- proof
  apply StatMech.Lattice.umEar_windowTurn_add K e a b c hab hbc

/--
[umEar_totalTurnZ_eq_window](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzEar.lean)
-/
@[path]
private lemma umEar_totalTurnZ_eq_window_eq
  {K : Set (Site 2)}
  {e : Dart}
  {p : ℕ} :
-- imply
  totalTurnZ K e p = umEar_windowTurn K e 0 p := by
-- proof
  apply StatMech.Lattice.umEar_totalTurnZ_eq_window K e p

/--
[umEar_totalTurnZ_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzEar.lean)
-/
@[path]
private lemma umEar_totalTurnZ_split_eq
  {K : Set (Site 2)}
  {e : Dart}
  {m p : ℕ}
-- given
  (hm : m ≤ p) :
-- imply
  totalTurnZ K e p = umEar_windowTurn K e 0 m + umEar_windowTurn K e m p := by
-- proof
  apply StatMech.Lattice.umEar_totalTurnZ_split K e m p hm

/--
[umEar_windowTurn_eq_range](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzEar.lean)
-/
@[path]
private lemma umEar_windowTurn_eq_range_eq
  {K : Set (Site 2)}
  {e : Dart}
  {a n : ℕ} :
-- imply
  umEar_windowTurn K e a (a + n) = ∑ i ∈ Finset.range n, turnZ K ((dartNext K)^[a + i] e) := by
-- proof
  apply StatMech.Lattice.umEar_windowTurn_eq_range K e a n

/--
[umEar_tail_turn_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzEar.lean)
-/
@[path]
private lemma umEar_tail_turn_eq_eq
  {K K' : Set (Site 2)}
  {e e' : Dart}
  {m m' n : ℕ}
-- given
  (hmatch : ∀ i, i < n → turnZ K ((dartNext K)^[m + i] e) = turnZ K' ((dartNext K')^[m' + i] e')) :
-- imply
  umEar_windowTurn K e m (m + n) = umEar_windowTurn K' e' m' (m' + n) := by
-- proof
  apply StatMech.Lattice.umEar_tail_turn_eq K K' e e' m m' n hmatch

/--
[umEar_contraction_turning_change](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzEar.lean)
-/
@[path]
private lemma umEar_contraction_turning_change_eq
  {K K' : Set (Site 2)}
  {e e' : Dart}
  {m m' n : ℕ}
-- given
  (hmatch : ∀ i, i < n → turnZ K ((dartNext K)^[m + i] e) = turnZ K' ((dartNext K')^[m' + i] e')) :
-- imply
  totalTurnZ K' e' (m' + n) = totalTurnZ K e (m + n) + (umEar_windowTurn K' e' 0 m' - umEar_windowTurn K e 0 m) := by
-- proof
  apply StatMech.Lattice.umEar_contraction_turning_change K K' e e' m m' n hmatch

/--
[umEar_contraction_preserves_turning](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzEar.lean)
-/
@[path]
private lemma umEar_contraction_preserves_turning_eq
  {K K' : Set (Site 2)}
  {e e' : Dart}
  {m m' n : ℕ}
-- given
  (hmatch : ∀ i, i < n → turnZ K ((dartNext K)^[m + i] e) = turnZ K' ((dartNext K')^[m' + i] e'))
  (hbal : umEar_windowTurn K' e' 0 m' = umEar_windowTurn K e 0 m) :
-- imply
  totalTurnZ K' e' (m' + n) = totalTurnZ K e (m + n) := by
-- proof
  apply StatMech.Lattice.umEar_contraction_preserves_turning K K' e e' m m' n hmatch hbal

/--
[umEar_windowTurn_eq_balance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzEar.lean)
-/
@[path]
private lemma umEar_windowTurn_eq_balance_eq
  {K : Set (Site 2)}
  {e : Dart}
  {a b : ℕ} :
-- imply
  umEar_windowTurn K e a b = umEar_windowRight K e a b - umEar_windowLeft K e a b := by
-- proof
  apply StatMech.Lattice.umEar_windowTurn_eq_balance K e a b

/--
[umEar_contraction_preserves_turning_balance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzEar.lean)
-/
@[path]
private lemma umEar_contraction_preserves_turning_balance_eq
  {K K' : Set (Site 2)}
  {e e' : Dart}
  {m m' n : ℕ}
-- given
  (hmatch : ∀ i, i < n → turnZ K ((dartNext K)^[m + i] e) = turnZ K' ((dartNext K')^[m' + i] e'))
  (hbal : umEar_windowRight K' e' 0 m' - umEar_windowLeft K' e' 0 m' = umEar_windowRight K e 0 m - umEar_windowLeft K e 0 m) :
-- imply
  totalTurnZ K' e' (m' + n) = totalTurnZ K e (m + n) := by
-- proof
  apply StatMech.Lattice.umEar_contraction_preserves_turning_balance K K' e e' m m' n hmatch hbal

/--
[umEar_extremeCell_ear_first_turn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzEar.lean)
-/
@[path]
private lemma umEar_extremeCell_ear_first_turn_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (hc : IsExtremeCell K c) :
-- imply
  turnZ K ((dartNext K)^[0] (leftDart c)) = -1 := by
-- proof
  apply StatMech.Lattice.umEar_extremeCell_ear_first_turn K c hc

/--
[umEar_extremeCell_one_le_windowLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzEar.lean)
-/
@[path]
private lemma umEar_extremeCell_one_le_windowLeft_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {m : ℕ}
-- given
  (hc : IsExtremeCell K c)
  (hm : 1 ≤ m) :
-- imply
  1 ≤ umEar_windowLeft K (leftDart c) 0 m := by
-- proof
  apply StatMech.Lattice.umEar_extremeCell_one_le_windowLeft K c hc m hm

/--
[umEar_domino_contracts_to_unitCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzEar.lean)
-/
@[path]
private lemma umEar_domino_contracts_to_unitCell_eq :
-- imply
  totalTurnZ domino dmD0 6 = totalTurnZ unitCell ucDart0 4 := by
-- proof
  apply StatMech.Lattice.umEar_domino_contracts_to_unitCell

/--
[umEar_domino_unitCell_totalTurnZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzEar.lean)
-/
@[path]
private lemma umEar_domino_unitCell_totalTurnZ_eq :
-- imply
  totalTurnZ domino dmD0 6 = -4 ∧ totalTurnZ unitCell ucDart0 4 = -4 := by
-- proof
  apply StatMech.Lattice.umEar_domino_unitCell_totalTurnZ


-- created on 2026-10-23
