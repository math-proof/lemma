/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Poset/LinearExtension.lean -/

import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.Extension.Linear

/-!
# Linear extensions of finite posets

All linear extensions of a finite poset, represented as bijective monotone
rank functions into `Fin (Fintype.card α)`. Every finite poset has a linear
extension (Szpilrajn), so the family is nonempty and its cardinality is a
valid denominator. Also provides maximal elements of a finset.
-/

namespace FinPoset

/-- All linear extensions of a finite poset, represented as bijective monotone
rank functions into its zero-based set of positions. -/
noncomputable def linearExtensions (α : Type*) [Fintype α] [PartialOrder α] :
    Finset (α → Fin (Fintype.card α)) := by
  classical
  exact Finset.univ.filter fun σ => Function.Bijective σ ∧ Monotone σ

/-- Membership characterization for `linearExtensions`. -/
theorem mem_linearExtensions (α : Type*) [Fintype α] [PartialOrder α]
    (σ : α → Fin (Fintype.card α)) :
    σ ∈ linearExtensions α ↔ Function.Bijective σ ∧ Monotone σ := by
  simp only [linearExtensions, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The Szpilrajn linear order on `α`, order-isomorphic to `Fin (card α)`. -/
noncomputable def linExtOrderIso (α : Type*) [Fintype α] [PartialOrder α] :
    LinearExtension α ≃o Fin (Fintype.card α) := by
  have : Fintype (LinearExtension α) := inferInstanceAs (Fintype α)
  have hcard : Fintype.card (LinearExtension α) = Fintype.card α :=
    Fintype.card_congr (Equiv.refl α : α ≃ LinearExtension α)
  exact (Fintype.orderIsoFinOfCardEq (LinearExtension α) rfl).symm.trans
    (Fin.castOrderIso hcard)

/-- A chosen linear extension via Szpilrajn: rank through `linExtOrderIso`. -/
noncomputable def someLinearExtension (α : Type*) [Fintype α] [PartialOrder α] :
    α → Fin (Fintype.card α) := fun x =>
  linExtOrderIso α (toLinearExtension x)

/-- The chosen linear extension is bijective. -/
theorem bijective_someLinearExtension (α : Type*) [Fintype α] [PartialOrder α] :
    Function.Bijective (someLinearExtension α) :=
  (linExtOrderIso α).toEquiv.bijective

/-- The chosen linear extension is monotone. -/
theorem monotone_someLinearExtension (α : Type*) [Fintype α] [PartialOrder α] :
    Monotone (someLinearExtension α) := fun _ _ h =>
  (linExtOrderIso α).monotone (toLinearExtension.monotone' h)

/-- Every finite poset has a linear extension. -/
theorem nonempty_linearExtensions (α : Type*) [Fintype α] [PartialOrder α] :
    (linearExtensions α).Nonempty :=
  ⟨someLinearExtension α, by
    rw [mem_linearExtensions]
    exact ⟨bijective_someLinearExtension α, monotone_someLinearExtension α⟩⟩

/-- The linear-extension count is positive: a valid denominator. -/
theorem card_linearExtensions_pos (α : Type*) [Fintype α] [PartialOrder α] :
    0 < (linearExtensions α).card :=
  Finset.card_pos.mpr (nonempty_linearExtensions α)

/-- Maximal elements of a finset in the ambient order. -/
noncomputable def maximalElements {P : Type*} [PartialOrder P]
    (A : Finset P) : Finset P := by
  classical
  exact A.filter fun x ↦ ∀ y ∈ A, x ≤ y → y = x

/-- Membership characterization for `maximalElements`. -/
theorem mem_maximalElements {P : Type*} [PartialOrder P] (A : Finset P)
    (x : P) : x ∈ maximalElements A ↔ x ∈ A ∧ ∀ y ∈ A, x ≤ y → y = x := by
  simp only [maximalElements, Finset.mem_filter]

end FinPoset
