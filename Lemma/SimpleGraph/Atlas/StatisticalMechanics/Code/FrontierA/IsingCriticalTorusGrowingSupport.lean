import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalTorusGrowingSupport
open Filter Finset Topology StatMech StatMech.FrontierA


/--
[exists_criticalTorusGrowingCompactCumulant_diagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalTorusGrowingSupport.lean)
-/
@[path]
private lemma exists_criticalTorusGrowingCompactCumulant_diagonal_eq
  {d : Nat}
  {A : Nat → Finset (Site d)}
  {a : Nat → Site d → Real}
-- given
  (hd : 2 < d) :
-- imply
  ∃ scale : Nat → Nat, Tendsto scale atTop atTop ∧ ∀ n order, order ≤ n → := by
-- proof
  apply StatMech.FrontierA.exists_criticalTorusGrowingCompactCumulant_diagonal hd A a

/--
[exists_criticalTorusGrowingCompactCumulant_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalTorusGrowingSupport.lean)
-/
@[path]
private lemma exists_criticalTorusGrowingCompactCumulant_tendsto_eq
  {d : Nat}
  {A : Nat → Finset (Site d)}
  {a : Nat → Site d → Real}
-- given
  (hd : 2 < d) :
-- imply
  ∃ scale : Nat → Nat, Tendsto scale atTop atTop ∧ ∀ order, Tendsto (fun n ↦ criticalTorusCompactWeightedCumulant (A n) (a n) (scale n) order - criticalFreeCompactWeightedCumulant (A n) (a n) order) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.exists_criticalTorusGrowingCompactCumulant_tendsto hd A a


-- created on 2026-10-23
