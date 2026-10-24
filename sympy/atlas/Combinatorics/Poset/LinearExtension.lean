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

/-- Maximal elements of a finset in the ambient order. -/
noncomputable def maximalElements {P : Type*} [PartialOrder P]
    (A : Finset P) : Finset P := by
  classical
  exact A.filter fun x ↦ ∀ y ∈ A, x ≤ y → y = x
end FinPoset
