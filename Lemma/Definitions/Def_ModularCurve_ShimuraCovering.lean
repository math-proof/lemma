import Lemma.Definitions.Def_ModularCurve_ShimuraSubgroup

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
theorem coe_inclusionBar {F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ)} (h : F₀ ≤ F₁)
    (x : laurentBaseChange L F₀) :
    (inclusionBar L h x : LaurentSeries L) = (x : LaurentSeries L) :=
  IntermediateField.coe_inclusion _ x

theorem ramificationIndexAlong_inclusionBar_refl (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (w : Place L (laurentBaseChange L F₀)) :
    Place.ramificationIndexAlong (inclusionBar L (le_refl F₀)) w = 1 := by
  classical
  unfold Place.ramificationIndexAlong Place.ramificationIndex
  have hid : ∀ f : laurentBaseChange L F₀, inclusionBar L (le_refl F₀) f = f :=
    fun f => Subtype.ext (coe_inclusionBar L (le_refl F₀) f)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  have h1 : (1 : ℕ) ∈ {n : ℕ | 0 < n ∧ ∃ f : laurentBaseChange L F₀, f ≠ 0 ∧
      w.ord (algebraMap (laurentBaseChange L F₀) (laurentBaseChange L F₀) f) = n} := by
    refine ⟨Nat.one_pos, (π : laurentBaseChange L F₀), ?_, ?_⟩
    · simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
    · show w.ord (inclusionBar L (le_refl F₀) π) = 1
      rw [hid, w.ord_coe_irreducible hπ]
  refine le_antisymm (Nat.sInf_le h1) ?_
  exact le_csInf ⟨1, h1⟩ fun n hn => hn.1

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

abbrev fieldBar : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) :=
  laurentBaseChange (AlgebraicClosure ℚ) D.field

def coverHom : modularFunctionFieldBar p →ₐ[AlgebraicClosure ℚ] D.fieldBar :=
  inclusionBar (AlgebraicClosure ℚ) D.base_le

@[simp]
theorem coe_coverHom (x : modularFunctionFieldBar p) :
    (D.coverHom x : LaurentSeries (AlgebraicClosure ℚ)) = (x : LaurentSeries (AlgebraicClosure ℚ)) :=
  coe_inclusionBar _ _ x

def KernelInputs : Prop :=
  ∃ (hint : D.coverHom.toRingHom.IsIntegral)
    (_ : HasPrincipalDivisors (AlgebraicClosure ℚ) D.fieldBar),
    FundamentalIdentityAlong (AlgebraicClosure ℚ) D.coverHom hint

open Classical in

def kernel : AddSubgroup (JZero p) :=
  if h : D.KernelInputs then
    letI := algebraAlong D.coverHom
    haveI := isScalarTower_along D.coverHom
    haveI := isIntegral_along D.coverHom h.1
    haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) D.fieldBar := h.2.1
    haveI : FundamentalIdentity (AlgebraicClosure ℚ) (modularFunctionFieldBar p) D.fieldBar :=
      h.2.2
    (Pic0.pullbackHom (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar p) D.fieldBar).ker
  else ⊥

theorem kernel_of_not (h : ¬ D.KernelInputs) : D.kernel = ⊥ := by
  rw [kernel, dif_neg h]

end ShimuraCoveringData

end ModularCurve

end
