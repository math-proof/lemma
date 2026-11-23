module

public import Mathlib
public import Def.NumberField_SelmerRepModP
public import Theorem.Rep.LevelArithmeticModP
public import Instance.NumberField_SelmerRepModP

public noncomputable section

set_option autoImplicit false

noncomputable section

open CategoryTheory IsDedekindDomain
open scoped NumberField NumberField.LevelArith Pointwise Rep

namespace NumberField.LevelArith

section Selmer

variable (E F : Type) [Field E] [Field F] [NumberField E] [NumberField F] [Algebra E F]
  (S : Finset (HeightOneSpectrum (𝓞 E))) (p : ℕ)

omit [NumberField E] [NumberField F] in
public theorem unitsModPow.mk_pow (x : Fˣ) : unitsModPow.mk F p (x ^ p) = 1 :=
  (QuotientGroup.eq_one_iff _).2 ⟨x, rfl⟩

omit [NumberField E] [NumberField F] in

public theorem unitsModPow.pow_eq_one (q : unitsModPow F p) : q ^ p = 1 := by
  obtain ⟨x, rfl⟩ := unitsModPow.mk_surjective F p q
  show (QuotientGroup.mk x : Fˣ ⧸ (powMonoidHom p : Fˣ →* Fˣ).range) ^ p = 1
  rw [← QuotientGroup.mk_pow]
  exact unitsModPow.mk_pow F p x

omit [NumberField E] [NumberField F] in

public theorem nsmul_additive_unitsModPow (a : Additive (unitsModPow F p)) : p • a = 0 :=
  Additive.toMul.injective (by rw [toMul_nsmul, toMul_zero]; exact unitsModPow.pow_eq_one F p _)

omit [NumberField E] [NumberField F] in

@[simp] public theorem smul_mk (σ : F ≃ₐ[E] F) (x : Fˣ) : σ • unitsModPow.mk F p x = unitsModPow.mk F p (σ • x) := rfl


public theorem mem_selmer_iff (x : Fˣ) : unitsModPow.mk F p x ∈ selmer E F S p ↔
    ∀ v : HeightOneSpectrum (𝓞 F), v ∉ NumberField.SUnits.placesAbove E F S →
      v.valuationOfNeZeroMod p (QuotientGroup.mk x : Fˣ ⧸ (powMonoidHom p : Fˣ →* Fˣ).range) = 1 := Iff.rfl


public theorem mem_selmerStable_iff (x : unitsModPow F p) : x ∈ selmerStable E F S p ↔ ∀ σ : F ≃ₐ[E] F, σ • x ∈ selmer E F S p := by
  simp only [selmerStable, Subgroup.mem_iInf, Subgroup.mem_comap, MulDistribMulAction.toMonoidHom_apply]

omit [NumberField E] in

public theorem smul_mem_selmerStable (τ : F ≃ₐ[E] F) {x : unitsModPow F p} (hx : x ∈ selmerStable E F S p) : τ • x ∈ selmerStable E F S p := by
  rw [mem_selmerStable_iff] at hx ⊢
  intro σ
  rw [← mul_smul]
  exact hx (σ * τ)


public theorem mem_selmerSubmodule (x : Additive (unitsModPow F p)) : x ∈ selmerSubmodule E F S p ↔ Additive.toMul x ∈ selmerStable E F S p := Iff.rfl


public theorem nsmul_selmer_eq_zero (x : selmerRepInt E F S p) : p • x = 0 :=
  Subtype.ext (nsmul_additive_unitsModPow F p _)

omit [NumberField E] in


@[simp] public theorem selmerRepInt_ρ_apply (σ : F ≃ₐ[E] F) (x : selmerRepInt E F S p) :
    (Subtype.val ((selmerRepInt E F S p).ρ σ x) : Additive (unitsModPow F p)) =
      Additive.ofMul (σ • Additive.toMul (Subtype.val x : Additive (unitsModPow F p))) := rfl


@[simp] public theorem selmerRepField_ρ_apply (σ : F ≃ₐ[E] F) (x : selmerRepField E F S p) :
    (Subtype.val ((selmerRepField E F S p).ρ σ x) : Additive (unitsModPow F p)) =
      Additive.ofMul (σ • Additive.toMul (Subtype.val x : Additive (unitsModPow F p))) := rfl

omit [NumberField E] in


public theorem mk_mem_selmerStable (u : NumberField.SUnits.sUnitsRep E F S) :
    unitsModPow.mk F p (NumberField.SUnits.val E F S u) ∈ selmerStable E F S p := by
  rw [mem_selmerStable_iff]
  intro σ
  rw [smul_mk, mem_selmer_iff]
  intro v hv
  have hval : v.valuation F ((σ • NumberField.SUnits.val E F S u : Fˣ) : F) = 1 :=
    (NumberField.SUnits.mem_sUnits_iff E F S _).1 (NumberField.SUnits.val_mem E F S u) σ v hv
  have h1 : v.valuationOfNeZero (σ • NumberField.SUnits.val E F S u) = 1 := by
    apply WithZero.coe_injective
    rw [HeightOneSpectrum.valuationOfNeZero_eq]
    exact hval
  have hmod :
      v.valuationOfNeZeroMod p
        (QuotientGroup.mk (σ • NumberField.SUnits.val E F S u) :
          Fˣ ⧸ (powMonoidHom p : Fˣ →* Fˣ).range) =
      (Int.quotientZMultiplesNatEquivZMod p).toMultiplicative.toMonoidHom
        (QuotientGroup.mk (s := AddSubgroup.toSubgroup (AddSubgroup.zmultiples (p : ℤ)))
          (v.valuationOfNeZero (σ • NumberField.SUnits.val E F S u))) :=
    rfl
  rw [hmod, h1, QuotientGroup.mk_one]
  erw [map_one]

omit [NumberField E] [NumberField F] in


public theorem smul_top_le_ker {k : Type} [CommRing k] {V W : Type} [AddCommGroup V] [AddCommGroup W] {iV : Module k V} {iW : Module k W}
    (f : V →ₗ[k] W) (hW : ∀ w : W, p • w = 0) : (p : k) • (⊤ : Submodule k V) ≤ LinearMap.ker f := by
  intro x hx
  obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
  rw [LinearMap.mem_ker, map_smul, Nat.cast_smul_eq_nsmul]
  exact hW _


public theorem fromSUnitsModP_hom_mk (u : NumberField.SUnits.sUnitsRep E F S) :
    (((fromSUnitsModP E F S p).hom (Submodule.Quotient.mk u)).1 : Additive (unitsModPow F p)) =
      Additive.ofMul (unitsModPow.mk F p (NumberField.SUnits.val E F S u)) := rfl

end Selmer

section Level

variable (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKL : K ≤ L) [Normal ↥K ↥(levelField K L hKL)]
  [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L] (S : Finset Nat.Primes) (p : ℕ)

