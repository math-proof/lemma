import Mathlib
import sympy.Basic
open Finset BigOperators
open scoped AddChar ComplexConjugate


namespace CharacterOrthogonality

/--
[orthogonality_group](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop1837.lean)
-/
@[path]
lemma orthogonality_group
  [AddCommGroup G]
  [Fintype G]
  [DecidableEq G]
  {g₁ g₂ : G} :
-- imply
  ∑ χ : AddChar G ℂ, χ g₁ * (starRingEnd ℂ) (χ g₂) = if g₁ = g₂ then (Fintype.card G : ℂ) else 0 := by
-- proof
  have key : ∀ χ : AddChar G ℂ, χ g₁ * (starRingEnd ℂ) (χ g₂) = χ (g₁ - g₂) := by
    intro χ
    rw [← AddChar.inv_apply_eq_conj, ← AddChar.map_neg_eq_inv,
      ← AddChar.map_add_eq_mul, sub_eq_add_neg]
  simp_rw [key, AddChar.sum_apply_eq_ite, sub_eq_zero]

end CharacterOrthogonality

namespace CharacterOrthogonality

/--
[orthogonality_group_normalized](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop1837.lean)
-/
@[path]
lemma orthogonality_group_normalized
  [AddCommGroup G]
  [Fintype G]
  [DecidableEq G]
  {g₁ g₂ : G} :
-- imply
  ((Fintype.card G : ℂ)⁻¹) * ∑ χ : AddChar G ℂ, χ g₁ * (starRingEnd ℂ) (χ g₂) = if g₁ = g₂ then 1 else 0 := by
-- proof
  rw [orthogonality_group]
  split_ifs <;> simp [Nat.cast_ne_zero.mpr Fintype.card_ne_zero]

end CharacterOrthogonality

namespace CharacterOrthogonality

/--
[orthogonality_char](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop1837.lean)
-/
@[path]
lemma orthogonality_char
  [AddCommGroup G]
  [Fintype G]
  {χ₁ χ₂ : AddChar G ℂ} :
-- imply
  ∑ g : G, χ₁ g * (starRingEnd ℂ) (χ₂ g) = if χ₁ = χ₂ then (Fintype.card G : ℂ) else 0 := by
-- proof
  have key : ∀ g : G, χ₁ g * (starRingEnd ℂ) (χ₂ g) = (χ₁ - χ₂) g := by
    intro g
    rw [AddChar.sub_apply, ← AddChar.inv_apply_eq_conj, ← AddChar.map_neg_eq_inv]
  simp_rw [key]
  classical
  rw [AddChar.sum_eq_ite]
  simp only [sub_eq_zero]

end CharacterOrthogonality

namespace CharacterOrthogonality

/--
[orthogonality_char_normalized](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop1837.lean)
-/
@[path]
lemma orthogonality_char_normalized
  [AddCommGroup G]
  [Fintype G]
  {χ₁ χ₂ : AddChar G ℂ} :
-- imply
  ((Fintype.card G : ℂ)⁻¹) * ∑ g : G, χ₁ g * (starRingEnd ℂ) (χ₂ g) = if χ₁ = χ₂ then 1 else 0 := by
-- proof
  rw [orthogonality_char]
  split_ifs <;> simp [Nat.cast_ne_zero.mpr Fintype.card_ne_zero]

end CharacterOrthogonality

namespace CharacterOrthogonality

/--
[character_orthogonality_relations](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop1837.lean)
-/
@[path]
lemma character_orthogonality_relations
  [AddCommGroup G]
  [Fintype G]
  [DecidableEq G] :
-- imply
  (∀ g₁ g₂ : G, ((Fintype.card G : ℂ)⁻¹) * ∑ χ : AddChar G ℂ, χ g₁ * (starRingEnd ℂ) (χ g₂) = if g₁ = g₂ then 1 else 0) ∧ (∀ χ₁ χ₂ : AddChar G ℂ, ((Fintype.card G : ℂ)⁻¹) * ∑ g : G, χ₁ g * (starRingEnd ℂ) (χ₂ g) = if χ₁ = χ₂ then 1 else 0) :=
-- proof
  ⟨orthogonality_group_normalized, orthogonality_char_normalized⟩

end CharacterOrthogonality


-- created on 2026-10-23
