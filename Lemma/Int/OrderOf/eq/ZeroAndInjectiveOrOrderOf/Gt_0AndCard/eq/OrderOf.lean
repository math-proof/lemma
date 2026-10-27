import Mathlib
import Initialize.Tactic.Attr.Basic
open Subgroup


namespace CyclicGroups

/--
[cyclic_subgroup_structure](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/CyclicGroups.lean)
-/
@[path]
private lemma cyclic_subgroup_structure
  [Group G]
  {g : G} :
-- imply
  (orderOf g = 0 ∧ Function.Injective (fun n : ℤ => g ^ n)) ∨ (0 < orderOf g ∧ Nat.card (zpowers g) = orderOf g) := by
-- proof
  obtain h | h := eq_or_lt_of_le (Nat.zero_le (orderOf g))
  · left
    exact ⟨h.symm, injective_zpow_iff_not_isOfFinOrder.mpr (orderOf_eq_zero_iff.mp h.symm)⟩
  · right
    exact ⟨h, Nat.card_zpowers g⟩

end CyclicGroups


-- created on 2026-10-23
-- updated on 2026-10-26
