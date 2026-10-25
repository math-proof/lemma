import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorCollisionStableSelector
open Finset StatMech StatMech.GrahamGHS StatMech.GrahamGHS.FourColor


/--
[GrahamFiberMinor_of_collisionStableBalancedSelector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorCollisionStableSelector.lean)
-/
@[path]
private lemma GrahamFiberMinor_of_collisionStableBalancedSelector_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
-- given
  (ends : I -> Sym2 W)
  (sigma : (↑m -> Fin 4) -> Finset I × Finset I)
  (hvalid : forall c, LeftPattern ends m {j, k} {k, l} k zero c -> let X := (sigma c).1 let Y := (sigma c).2 X ⊆ colorClass m c 1 ∪ colorClass m c 2 ∧ Y ⊆ colorClass m c 0 ∪ colorClass m c 3 ∧ sources ends X = {k, l} ∧ sources ends Y = ∅ ∧ RowsDisconnect ends m (balancedSwap m X Y c) k zero)
  (hstable : forall c d, LeftPattern ends m {j, k} {k, l} k zero c -> LeftPattern ends m {j, k} {k, l} k zero d -> balancedSwap m (sigma c).1 (sigma c).2 c = balancedSwap m (sigma d).1 (sigma d).2 d -> sigma c = sigma d) :
-- imply
  GrahamFiberMinor ends m j k l zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.GrahamFiberMinor_of_collisionStableBalancedSelector ends m j k l zero sigma hvalid hstable


-- created on 2026-10-23
