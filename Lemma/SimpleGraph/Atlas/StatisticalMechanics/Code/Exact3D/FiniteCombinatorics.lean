import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCombinatorics
open StatMech StatMech.Exact3D


/--
[card_le_card_of_injective_rankedPrefix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCombinatorics.lean)
-/
@[path]
private lemma card_le_card_of_injective_rankedPrefix_eq
  {target : Finset Slot}
  {n k : ℕ}
  {slotAt : Fin n → Slot}
-- given
  (hk : k ≤ n)
  (hinj : Function.Injective slotAt)
  (hprefix : ∀ i : Fin n, (i : ℕ) < k → slotAt i ∈ target) :
-- imply
  k ≤ target.card := by
-- proof
  apply StatMech.Exact3D.card_le_card_of_injective_rankedPrefix target slotAt hk hinj hprefix

/--
[exists_sortedFinsetEnumeration](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCombinatorics.lean)
-/
@[path]
private lemma exists_sortedFinsetEnumeration_eq
  {s : Finset α}
  {score : α → ℝ} :
-- imply
  ∃ itemAt : Fin s.card → α, (∀ i, itemAt i ∈ s) ∧ Function.Injective itemAt ∧ (∀ x, x ∈ s → ∃ i, itemAt i = x) ∧ (∀ i j : Fin s.card, (i : ℕ) ≤ (j : ℕ) → score (itemAt j) ≤ score (itemAt i)) := by
-- proof
  apply StatMech.Exact3D.exists_sortedFinsetEnumeration s score

/--
[sortedEnumeration_mem_thresholdTail_of_lt_filter_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCombinatorics.lean)
-/
@[path]
private lemma sortedEnumeration_mem_thresholdTail_of_lt_filter_card_eq
  {s : Finset α}
  {score : α → ℝ}
  {itemAt : Fin s.card → α}
  {threshold : ℝ}
  {i : Fin s.card}
-- given
  (hitemSurj : ∀ x, x ∈ s → ∃ i, itemAt i = x)
  (hitemSorted : ∀ (i j : Fin s.card), (i : ℕ) ≤ (j : ℕ) → score (itemAt j) ≤ score (itemAt i))
  (hi : (i : ℕ) < (s.filter (fun x => threshold ≤ score x)).card) :
-- imply
  threshold ≤ score (itemAt i) := by
-- proof
  apply StatMech.Exact3D.sortedEnumeration_mem_thresholdTail_of_lt_filter_card s score itemAt hitemSurj hitemSorted i hi


-- created on 2026-10-23
