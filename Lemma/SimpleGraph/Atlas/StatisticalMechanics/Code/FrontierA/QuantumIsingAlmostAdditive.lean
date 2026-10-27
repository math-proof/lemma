import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingAlmostAdditive.Part2
open Filter Set StatMech StatMech.FrontierA StatMech.FrontierA.QuantumIsingAlmostAdditive


/--
[nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingAlmostAdditive.lean)
-/
@[path]
private lemma nonneg_eq
  {u : Nat -> Real}
  {c : Real}
-- given
  (h : QuantumIsingAlmostAdditive u c) :
-- imply
  0 ≤ c := by
-- proof
  apply StatMech.FrontierA.QuantumIsingAlmostAdditive.nonneg h

/--
[lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingAlmostAdditive.lean)
-/
@[path]
private lemma lower_eq
  {u : Nat -> Real}
  {c : Real}
  {m n : Nat}
-- given
  (h : QuantumIsingAlmostAdditive u c) :
-- imply
  u m + u n - c ≤ u (m + n) := by
-- proof
  apply StatMech.FrontierA.QuantumIsingAlmostAdditive.lower h m n

/--
[upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingAlmostAdditive.lean)
-/
@[path]
private lemma upper_eq
  {u : Nat -> Real}
  {c : Real}
  {m n : Nat}
-- given
  (h : QuantumIsingAlmostAdditive u c) :
-- imply
  u (m + n) ≤ u m + u n + c := by
-- proof
  apply StatMech.FrontierA.QuantumIsingAlmostAdditive.upper h m n

/--
[shift_subadditive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingAlmostAdditive.lean)
-/
@[path]
private lemma shift_subadditive_eq
  {u : Nat -> Real}
  {c : Real}
-- given
  (h : QuantumIsingAlmostAdditive u c) :
-- imply
  Subadditive (fun n => u n + c) := by
-- proof
  apply StatMech.FrontierA.QuantumIsingAlmostAdditive.shift_subadditive h

/--
[neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingAlmostAdditive.lean)
-/
@[path]
private lemma neg_eq
  {u : Nat -> Real}
  {c : Real}
-- given
  (h : QuantumIsingAlmostAdditive u c) :
-- imply
  QuantumIsingAlmostAdditive (fun n => -u n) c := by
-- proof
  apply StatMech.FrontierA.QuantumIsingAlmostAdditive.neg h

/--
[shift_bddBelow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingAlmostAdditive.lean)
-/
@[path]
private lemma shift_bddBelow_eq
  {u : Nat -> Real}
  {c : Real}
-- given
  (h : QuantumIsingAlmostAdditive u c) :
-- imply
  BddBelow (Set.range fun n => (u n + c) / n) := by
-- proof
  apply StatMech.FrontierA.QuantumIsingAlmostAdditive.shift_bddBelow h

/--
[tendsto_limit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingAlmostAdditive.lean)
-/
@[path]
private lemma tendsto_limit_eq
  {u : Nat -> Real}
  {c : Real}
-- given
  (h : QuantumIsingAlmostAdditive u c) :
-- imply
  Tendsto (fun n => u n / n) atTop (nhds h.limit) := by
-- proof
  apply StatMech.FrontierA.QuantumIsingAlmostAdditive.tendsto_limit h

/--
[abs_limit_sub_div_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingAlmostAdditive.lean)
-/
@[path]
private lemma abs_limit_sub_div_le_eq
  {u : Nat -> Real}
  {c : Real}
  {L : Nat}
-- given
  (h : QuantumIsingAlmostAdditive u c)
  (hL : L ≠ 0) :
-- imply
  |h.limit - u L / L| ≤ c / L := by
-- proof
  apply StatMech.FrontierA.QuantumIsingAlmostAdditive.abs_limit_sub_div_le h hL


-- created on 2026-10-23
