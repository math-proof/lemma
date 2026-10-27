import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.ShermanGenericCancellation.Part3
open StatMech StatMech.Onsager


/--
[ons_summable_rootedListTerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanGenericCancellation.lean)
-/
@[path]
private lemma ons_summable_rootedListTerm_eq
  [Fintype E]
  [DecidableEq E]
  {Lambda : Matrix E E ℂ}
  {e r : E}
-- given
  (her : e ≠ r)
  (hsum : Summable fun s => ‖ons_firstReturnWeight Lambda e r s‖)
  (hsmall : ∑' s, ‖ons_firstReturnWeight Lambda e r s‖ < 1) :
-- imply
  Summable fun w : {w : List E // ons_validRootedList e r w} => ons_rootedListTerm Lambda e w.1 := by
-- proof
  apply StatMech.Onsager.ons_summable_rootedListTerm Lambda e r her hsum hsmall

/--
[ons_rootedListSeries_eq_geometric](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanGenericCancellation.lean)
-/
@[path]
private lemma ons_rootedListSeries_eq_geometric_eq
  [Fintype E]
  [DecidableEq E]
  {Lambda : Matrix E E ℂ}
  {e r : E}
-- given
  (her : e ≠ r)
  (hsum : Summable fun s => ‖ons_firstReturnWeight Lambda e r s‖)
  (hsmall : ∑' s, ‖ons_firstReturnWeight Lambda e r s‖ < 1) :
-- imply
  (∑' w : {w : List E // ons_validRootedList e r w}, ons_rootedListTerm Lambda e w.1) = ∑' k : ℕ, (∑' s, ons_firstReturnWeight Lambda e r s) ^ (k + 1) / (k + 1) := by
-- proof
  apply StatMech.Onsager.ons_rootedListSeries_eq_geometric Lambda e r her hsum hsmall


-- created on 2026-10-23
