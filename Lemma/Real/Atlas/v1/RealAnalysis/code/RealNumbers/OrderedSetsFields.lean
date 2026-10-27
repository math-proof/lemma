import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.RealAnalysis.code.RealNumbers.OrderedSetsFields
open OrderedSetsFields RealNumbers


namespace OrderedSetsFields

/--
[bounded_above_below_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/RealNumbers/OrderedSetsFields.lean)
-/
@[path]
lemma bounded_above_below_iff
  [Preorder α]
  {E : Set α} :
-- imply
  (BddAbove E ↔ ∃ b, ∀ x ∈ E, x ≤ b) ∧ (BddBelow E ↔ ∃ c, ∀ x ∈ E, c ≤ x) := by
-- proof
  exact ⟨by simp [BddAbove, upperBounds, Set.Nonempty],
    by simp [BddBelow, lowerBounds, Set.Nonempty]⟩

end OrderedSetsFields

namespace OrderedSetsFields

/--
[ordered_field_axioms](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/RealNumbers/OrderedSetsFields.lean)
-/
@[path]
lemma ordered_field_axioms
  {F : Type*}
  [Field F]
  [LinearOrder F]
  [IsStrictOrderedRing F] :
-- imply
  (∀ x y z : F, x < y → x + z < y + z) ∧ (∀ x y : F, 0 < x → 0 < y → 0 < x * y) :=
-- proof
  ⟨fun _ _ z h => add_lt_add_left h z, fun _ _ hx hy => mul_pos hx hy⟩
end OrderedSetsFields


namespace RealNumbers

/--
[field_axioms](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/RealNumbers/OrderedSetsFields.lean)
-/
@[path]
lemma field_axioms
  {F : Type*}
  [Field F] :
-- imply
  (∀ x y : F, x + y = y + x) ∧ (∀ x y z : F, (x + y) + z = x + (y + z)) ∧ (∃ zero : F, ∀ x, zero + x = x) ∧ (∀ x : F, ∃ y, x + y = 0) ∧ (∀ x y : F, x * y = y * x) ∧ (∀ x y z : F, (x * y) * z = x * (y * z)) ∧ (∃ one : F, ∀ x, one * x = x) ∧ (∀ x : F, x ≠ 0 → ∃ y, x * y = 1) ∧ (∀ x y z : F, (x + y) * z = x * z + y * z) := by
-- proof
  refine ⟨add_comm, add_assoc, ⟨0, zero_add⟩, fun x => ⟨-x, add_neg_cancel x⟩,
    mul_comm, mul_assoc, ⟨1, one_mul⟩, fun x hx => ⟨x⁻¹, mul_inv_cancel₀ hx⟩, add_mul⟩

end RealNumbers


-- created on 2026-10-23
