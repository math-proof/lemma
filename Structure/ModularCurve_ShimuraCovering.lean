import Structure.ModularCurve_ShimuraSubgroup

set_option autoImplicit false

noncomputable section

open IntermediateField AlgebraicCurve

namespace ModularCurve

section Supply

variable (L : Type*) [Field L] [Algebra ℚ L]

private theorem laurentBaseChange_mono_of_le {F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ)}
    (h : F₀ ≤ F₁) : laurentBaseChange L F₀ ≤ laurentBaseChange L F₁ := by
  rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
  rintro _ ⟨y, hy, rfl⟩
  exact coeffEmb_mem_laurentBaseChange L (h hy)

def inclusionBar {F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ)} (h : F₀ ≤ F₁) :
    laurentBaseChange L F₀ →ₐ[L] laurentBaseChange L F₁ :=
  IntermediateField.inclusion (laurentBaseChange_mono_of_le L h)

@[simp]


end Supply

section Carrier

variable (p : ℕ) [Fact p.Prime]

structure ShimuraCoveringData where

  field : IntermediateField ℚ (LaurentSeries ℚ)

  base_le : modularFunctionFieldFull p ≤ field

  deck : (ZMod p)ˣ →* (field ≃ₐ[ℚ] field)

  deck_apply_eq_self : ∀ (d : (ZMod p)ˣ) (x : field),
    (x : LaurentSeries ℚ) ∈ modularFunctionFieldFull p → deck d x = x

  mem_base_of_forall_deck_apply_eq : ∀ x : field,
    (∀ d : (ZMod p)ˣ, deck d x = x) → (x : LaurentSeries ℚ) ∈ modularFunctionFieldFull p

  card_range_deck : Nat.card deck.range = eisensteinNumerator p

  unramified : ∀ w : Place (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) field),
    Place.ramificationIndexAlong (inclusionBar (AlgebraicClosure ℚ) base_le) w = 1

end Carrier

namespace ShimuraCoveringData

variable {p : ℕ} [Fact p.Prime] (D : ShimuraCoveringData p)

structure LiftData (ℓ : ℕ) [Fact ℓ.Prime] where

  sup_eq_map_sup : D.field ⊔ modularFunctionFieldFull (p * ℓ)
      = D.field.map (qExpandₐ ℓ) ⊔ modularFunctionFieldFull (p * ℓ)

  deckUp : (ZMod p)ˣ →* (↥(D.field ⊔ modularFunctionFieldFull (p * ℓ))
      ≃ₐ[ℚ] ↥(D.field ⊔ modularFunctionFieldFull (p * ℓ)))

  coe_deckUp_inclusion : ∀ (d : (ZMod p)ˣ) (x : D.field),
    (deckUp d (IntermediateField.inclusion le_sup_left x) : LaurentSeries ℚ)
      = (D.deck d x : LaurentSeries ℚ)

  deckUp_apply_eq_self : ∀ (d : (ZMod p)ˣ) (y : ↥(D.field ⊔ modularFunctionFieldFull (p * ℓ))),
    (y : LaurentSeries ℚ) ∈ modularFunctionFieldFull (p * ℓ) → deckUp d y = y

  coe_deckUp_qExpand : ∀ (d : (ZMod p)ˣ) (x : D.field)
    (hx : qExpand ℚ ℓ (x : LaurentSeries ℚ) ∈ D.field ⊔ modularFunctionFieldFull (p * ℓ)),
    (deckUp d ⟨qExpand ℚ ℓ (x : LaurentSeries ℚ), hx⟩ : LaurentSeries ℚ)
      = qExpand ℚ ℓ (D.deck d x : LaurentSeries ℚ)


open Classical in


end ShimuraCoveringData

end ModularCurve

end
