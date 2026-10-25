import Mathlib
import Lemma.NumberField.LevelArithmeticModP
import Instance.NumberField_SelmerRepModP

set_option autoImplicit false

noncomputable section

open CategoryTheory IsDedekindDomain
open scoped NumberField NumberField.LevelArith Pointwise

namespace NumberField.LevelArith

section Selmer

variable (E F : Type) [Field E] [Field F] [NumberField E] [NumberField F] [Algebra E F]
  (S : Finset (HeightOneSpectrum (𝓞 E))) (p : ℕ)

def unitsModPow : Type := Fˣ ⧸ (powMonoidHom p : Fˣ →* Fˣ).range

abbrev unitsModPow.mk (x : Fˣ) : unitsModPow F p := (QuotientGroup.mk x : Fˣ ⧸ (powMonoidHom p : Fˣ →* Fˣ).range)

omit [NumberField E] [NumberField F] in
theorem unitsModPow.mk_surjective : Function.Surjective (unitsModPow.mk F p) := QuotientGroup.mk_surjective

omit [NumberField E] [NumberField F] in
theorem unitsModPow.mk_pow (x : Fˣ) : unitsModPow.mk F p (x ^ p) = 1 :=
  (QuotientGroup.eq_one_iff _).2 ⟨x, rfl⟩

omit [NumberField E] [NumberField F] in
theorem unitsModPow.pow_eq_one (q : unitsModPow F p) : q ^ p = 1 := by
  obtain ⟨x, rfl⟩ := unitsModPow.mk_surjective F p q
  show (QuotientGroup.mk x : Fˣ ⧸ (powMonoidHom p : Fˣ →* Fˣ).range) ^ p = 1
  rw [← QuotientGroup.mk_pow]
  exact unitsModPow.mk_pow F p x

omit [NumberField E] [NumberField F] in
theorem nsmul_additive_unitsModPow (a : Additive (unitsModPow F p)) : p • a = 0 :=
  Additive.toMul.injective (by rw [toMul_nsmul, toMul_zero]; exact unitsModPow.pow_eq_one F p _)

omit [NumberField E] [NumberField F] in
theorem range_powMonoidHom_le_comap (σ : F ≃ₐ[E] F) :
    (powMonoidHom p : Fˣ →* Fˣ).range ≤ ((powMonoidHom p : Fˣ →* Fˣ).range).comap (MulDistribMulAction.toMonoidHom Fˣ σ) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨σ • x, by rw [MulDistribMulAction.toMonoidHom_apply, powMonoidHom_apply, powMonoidHom_apply, smul_pow']⟩

def unitsModPowMap (σ : F ≃ₐ[E] F) : unitsModPow F p →* unitsModPow F p :=
  (QuotientGroup.map _ _ (MulDistribMulAction.toMonoidHom Fˣ σ) (range_powMonoidHom_le_comap E F p σ) :
    (Fˣ ⧸ (powMonoidHom p : Fˣ →* Fˣ).range) →* (Fˣ ⧸ (powMonoidHom p : Fˣ →* Fˣ).range))

omit [NumberField E] [NumberField F] in
@[simp] theorem unitsModPowMap_mk (σ : F ≃ₐ[E] F) (x : Fˣ) : unitsModPowMap E F p σ (unitsModPow.mk F p x) = unitsModPow.mk F p (σ • x) := rfl

omit [NumberField E] [NumberField F] in
@[simp] theorem smul_mk (σ : F ≃ₐ[E] F) (x : Fˣ) : σ • unitsModPow.mk F p x = unitsModPow.mk F p (σ • x) := rfl

def selmer : Subgroup (unitsModPow F p) :=
  (selmerGroup (R := 𝓞 F) (K := F) (S := NumberField.SUnits.placesAbove E F S) (n := p) : Subgroup (Fˣ ⧸ (powMonoidHom p : Fˣ →* Fˣ).range))

omit [NumberField E] in
theorem mem_selmer_iff (x : Fˣ) : unitsModPow.mk F p x ∈ selmer E F S p ↔
    ∀ v : HeightOneSpectrum (𝓞 F), v ∉ NumberField.SUnits.placesAbove E F S →
      v.valuationOfNeZeroMod p (QuotientGroup.mk x : Fˣ ⧸ (powMonoidHom p : Fˣ →* Fˣ).range) = 1 := Iff.rfl

def selmerStable : Subgroup (unitsModPow F p) :=
  ⨅ σ : F ≃ₐ[E] F, (selmer E F S p).comap (MulDistribMulAction.toMonoidHom (unitsModPow F p) σ)

omit [NumberField E] in
theorem mem_selmerStable_iff (x : unitsModPow F p) : x ∈ selmerStable E F S p ↔ ∀ σ : F ≃ₐ[E] F, σ • x ∈ selmer E F S p := by
  simp only [selmerStable, Subgroup.mem_iInf, Subgroup.mem_comap, MulDistribMulAction.toMonoidHom_apply]

omit [NumberField E] in
theorem smul_mem_selmerStable (τ : F ≃ₐ[E] F) {x : unitsModPow F p} (hx : x ∈ selmerStable E F S p) : τ • x ∈ selmerStable E F S p := by
  rw [mem_selmerStable_iff] at hx ⊢
  intro σ
  rw [← mul_smul]
  exact hx (σ * τ)

def selmerSubmodule : Submodule ℤ (Additive (unitsModPow F p)) := (Subgroup.toAddSubgroup (selmerStable E F S p)).toIntSubmodule

omit [NumberField E] in
theorem mem_selmerSubmodule (x : Additive (unitsModPow F p)) : x ∈ selmerSubmodule E F S p ↔ Additive.toMul x ∈ selmerStable E F S p := Iff.rfl

abbrev selmerRepInt : Rep ℤ (F ≃ₐ[E] F) :=
  Rep.of ((Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (unitsModPow F p)).ρ.subrepresentation (selmerSubmodule E F S p)
    fun σ _ hx => smul_mem_selmerStable E F S p σ hx)

omit [NumberField E] in
theorem nsmul_selmer_eq_zero (x : selmerRepInt E F S p) : p • x = 0 :=
  Subtype.ext (nsmul_additive_unitsModPow F p _)

omit [NumberField E] in

@[simp] theorem selmerRepInt_ρ_apply (σ : F ≃ₐ[E] F) (x : selmerRepInt E F S p) :
    (Subtype.val ((selmerRepInt E F S p).ρ σ x) : Additive (unitsModPow F p)) =
      Additive.ofMul (σ • Additive.toMul (Subtype.val x : Additive (unitsModPow F p))) := rfl

abbrev selmerRepField : Rep (ZMod p) (F ≃ₐ[E] F) := Rep.of (toZMod p (selmerRepInt E F S p).ρ)

omit [NumberField E] in

@[simp] theorem selmerRepField_ρ_apply (σ : F ≃ₐ[E] F) (x : selmerRepField E F S p) :
    (Subtype.val ((selmerRepField E F S p).ρ σ x) : Additive (unitsModPow F p)) =
      Additive.ofMul (σ • Additive.toMul (Subtype.val x : Additive (unitsModPow F p))) := rfl

omit [NumberField E] in

theorem mk_mem_selmerStable (u : NumberField.SUnits.sUnitsRep E F S) :
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
  simp only [HeightOneSpectrum.valuationOfNeZeroMod, MonoidHom.coe_comp, Function.comp_apply]
  erw [QuotientGroup.map_mk, h1, QuotientGroup.mk_one, map_one]

omit [NumberField E] [NumberField F] in

theorem smul_top_le_ker {k : Type} [CommRing k] {V W : Type} [AddCommGroup V] [AddCommGroup W] {iV : Module k V} {iW : Module k W}
    (f : V →ₗ[k] W) (hW : ∀ w : W, p • w = 0) : (p : k) • (⊤ : Submodule k V) ≤ LinearMap.ker f := by
  intro x hx
  obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
  rw [LinearMap.mem_ker, map_smul, Nat.cast_smul_eq_nsmul]
  exact hW _

def fromSUnitsLinear : NumberField.SUnits.sUnitsRep E F S →ₗ[ℤ] selmerRepInt E F S p where
  toFun u := ⟨Additive.ofMul (unitsModPow.mk F p (NumberField.SUnits.val E F S u)), mk_mem_selmerStable E F S p u⟩
  map_add' _ _ := rfl
  map_smul' n u := Subtype.ext (by
    change Additive.ofMul (unitsModPow.mk F p (NumberField.SUnits.val E F S (n • u))) =
      n • Additive.ofMul (unitsModPow.mk F p (NumberField.SUnits.val E F S u))
    rw [NumberField.SUnits.val_zsmul]
    exact (QuotientGroup.mk_zpow ((powMonoidHom p : Fˣ →* Fˣ).range) (NumberField.SUnits.val E F S u) n :))

def fromSUnitsModP : repModP p (NumberField.SUnits.sUnitsRep E F S) ⟶ selmerRepField E F S p :=
  Rep.ofHom ⟨(Submodule.liftQ _ (fromSUnitsLinear E F S p) (smul_top_le_ker p _ (nsmul_selmer_eq_zero E F S p))).toAddMonoidHom.toZModLinearMap p,
    fun σ => LinearMap.ext fun x => by
      obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rfl⟩

omit [NumberField E] in
theorem fromSUnitsModP_hom_mk (u : NumberField.SUnits.sUnitsRep E F S) :
    (((fromSUnitsModP E F S p).hom (Submodule.Quotient.mk u)).1 : Additive (unitsModPow F p)) =
      Additive.ofMul (unitsModPow.mk F p (NumberField.SUnits.val E F S u)) := rfl

end Selmer

section Level

variable (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKL : K ≤ L) [Normal ↥K ↥(levelField K L hKL)]
  [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L] (S : Finset Nat.Primes) (p : ℕ)

abbrev selmerRep : Rep (ZMod p) ↥K.fixingSubgroup :=
  inflLevel K L hKL (selmerRepField ↥K ↥(levelField K L hKL) (placesOverPrimesFinset ↥K S) p)

abbrev unitsModPToSelmerRep : unitsModP K L hKL S p ⟶ selmerRep K L hKL S p :=
  (Rep.resFunctor (levelGal K L hKL)).map (fromSUnitsModP ↥K ↥(levelField K L hKL) (placesOverPrimesFinset ↥K S) p)

end Level

end NumberField.LevelArith

end
