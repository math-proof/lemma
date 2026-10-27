import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCycleComponentExchange.Part2
open Finset StatMech StatMech.GrahamGHS StatMech.GrahamGHS.FourColor


/--
[cyclePairComponentExchange_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCycleComponentExchange.lean)
-/
@[path]
private lemma cyclePairComponentExchange_card_le_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I → Sym2 W}
  {K L : Finset I}
  {u v : W}
-- given
  (hKL : Disjoint K L) :
-- imply
  Fintype.card (boundarySector ends K ∅ × boundarySector ends L ∅) ≤ Fintype.card (boundarySector ends ((K \ edgeComponent ends K u) ∪ edgeComponent ends L v) ∅ × boundarySector ends ((L \ edgeComponent ends L v) ∪ edgeComponent ends K u) ∅) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.cyclePairComponentExchange_card_le ends K L u v hKL

/--
[cycleSpaceWeight_componentExchange_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCycleComponentExchange.lean)
-/
@[path]
private lemma cycleSpaceWeight_componentExchange_le_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I → Sym2 W}
  {K L : Finset I}
  {u v : W}
-- given
  (hKL : Disjoint K L) :
-- imply
  Fintype.card (boundarySector ends K ∅) * Fintype.card (boundarySector ends L ∅) ≤ Fintype.card (boundarySector ends ((K \ edgeComponent ends K u) ∪ edgeComponent ends L v) ∅) * Fintype.card (boundarySector ends ((L \ edgeComponent ends L v) ∪ edgeComponent ends K u) ∅) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.cycleSpaceWeight_componentExchange_le ends K L u v hKL

/--
[rowSupportWeight_le_componentExchange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCycleComponentExchange.lean)
-/
@[path]
private lemma rowSupportWeight_le_componentExchange_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I → Sym2 W}
  {m K : Finset I}
  {k zero : W}
-- given
  (hKm : K ⊆ m) :
-- imply
  rowSupportWeight ends m K ≤ rowSupportWeight ends m (exchangeFirstRow ends K (m \ K) k zero) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rowSupportWeight_le_componentExchange ends m K k zero hKm

/--
[componentExchange_eq_of_eq_support_and_components](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCycleComponentExchange.lean)
-/
@[path]
private lemma componentExchange_eq_of_eq_support_and_components_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I → Sym2 W}
  {m : Finset I}
  {k zero : W}
  {K₁ K₂ : Finset I}
-- given
  (hsupport : exchangeFirstRow ends K₁ (m \ K₁) k zero = exchangeFirstRow ends K₂ (m \ K₂) k zero)
  (hzero : edgeComponent ends K₁ zero = edgeComponent ends K₂ zero)
  (hk : edgeComponent ends (m \ K₁) k = edgeComponent ends (m \ K₂) k) :
-- imply
  K₁ = K₂ := by
-- proof
  apply StatMech.GrahamGHS.FourColor.componentExchange_eq_of_eq_support_and_components ends m k zero hsupport hzero hk


-- created on 2026-10-23
