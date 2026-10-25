import Lemma.AutomorphicForm.SmoothCuspRealization

set_option autoImplicit false

open IsDedekindDomain NumberField

noncomputable section

namespace AutomorphicForm

namespace HeckeEigensystem

variable {F : Type*} [Field F] [NumberField F]

def cNorm (v : HeightOneSpectrum (𝓞 F)) : ℂ := (Ideal.absNorm v.asIdeal : ℂ)

theorem cNorm_ne_zero (v : HeightOneSpectrum (𝓞 F)) : cNorm v ≠ 0 := by
  have hN : Ideal.absNorm v.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
  rw [cNorm, Ne, Nat.cast_eq_zero]
  exact hN

def toRawCentral (Φ : HeckeEigensystem F ℂ) : HeckeEigensystem F ℂ where
  level := Φ.level
  level_ne_bot := Φ.level_ne_bot
  a := Φ.a
  b := fun v => (cNorm v)⁻¹ * Φ.b v

def ofRawCentral (Ψ : HeckeEigensystem F ℂ) : HeckeEigensystem F ℂ where
  level := Ψ.level
  level_ne_bot := Ψ.level_ne_bot
  a := Ψ.a
  b := fun v => cNorm v * Ψ.b v

@[simp] theorem toRawCentral_level (Φ : HeckeEigensystem F ℂ) : Φ.toRawCentral.level = Φ.level := rfl
@[simp] theorem toRawCentral_a (Φ : HeckeEigensystem F ℂ) (v : HeightOneSpectrum (𝓞 F)) :
    Φ.toRawCentral.a v = Φ.a v := rfl
@[simp] theorem toRawCentral_b (Φ : HeckeEigensystem F ℂ) (v : HeightOneSpectrum (𝓞 F)) :
    Φ.toRawCentral.b v = (cNorm v)⁻¹ * Φ.b v := rfl
@[simp] theorem ofRawCentral_level (Ψ : HeckeEigensystem F ℂ) : Ψ.ofRawCentral.level = Ψ.level := rfl
@[simp] theorem ofRawCentral_a (Ψ : HeckeEigensystem F ℂ) (v : HeightOneSpectrum (𝓞 F)) :
    Ψ.ofRawCentral.a v = Ψ.a v := rfl
@[simp] theorem ofRawCentral_b (Ψ : HeckeEigensystem F ℂ) (v : HeightOneSpectrum (𝓞 F)) :
    Ψ.ofRawCentral.b v = cNorm v * Ψ.b v := rfl

@[simp] theorem ofRawCentral_toRawCentral (Φ : HeckeEigensystem F ℂ) :
    Φ.toRawCentral.ofRawCentral = Φ := by
  cases Φ with
  | mk level hl a b =>
    simp only [toRawCentral, ofRawCentral, mk.injEq, true_and]
    funext v
    rw [← mul_assoc, mul_inv_cancel₀ (cNorm_ne_zero v), one_mul]

@[simp] theorem toRawCentral_ofRawCentral (Ψ : HeckeEigensystem F ℂ) :
    Ψ.ofRawCentral.toRawCentral = Ψ := by
  cases Ψ with
  | mk level hl a b =>
    simp only [toRawCentral, ofRawCentral, mk.injEq, true_and]
    funext v
    rw [← mul_assoc, inv_mul_cancel₀ (cNorm_ne_zero v), one_mul]

theorem toRawCentral_injective : Function.Injective (toRawCentral (F := F)) := fun Φ Φ' h => by
  rw [← ofRawCentral_toRawCentral Φ, h, ofRawCentral_toRawCentral]

theorem AgreesAwayFromFinite.toRawCentral {Φ Φ' : HeckeEigensystem F ℂ}
    (h : AgreesAwayFromFinite Φ Φ') : AgreesAwayFromFinite Φ.toRawCentral Φ'.toRawCentral := by
  obtain ⟨S, hS⟩ := h
  exact ⟨S, fun v hv => ⟨(hS v hv).1, congrArg ((cNorm v)⁻¹ * ·) (hS v hv).2⟩⟩

theorem AgreesAwayFromFinite.of_toRawCentral {Φ Φ' : HeckeEigensystem F ℂ}
    (h : AgreesAwayFromFinite Φ.toRawCentral Φ'.toRawCentral) : AgreesAwayFromFinite Φ Φ' := by
  obtain ⟨S, hS⟩ := h
  exact ⟨S, fun v hv =>
    ⟨(hS v hv).1, mul_left_cancel₀ (inv_ne_zero (cNorm_ne_zero v)) (hS v hv).2⟩⟩

end HeckeEigensystem

variable (F : Type) [Field F] [NumberField F]

def IsArithCuspRealizable (pins : CarrierPins F) (Φ : HeckeEigensystem F ℂ) : Prop :=
  IsSmoothCuspRealizable F pins Φ.toRawCentral

theorem isArithCuspRealizable_iff (pins : CarrierPins F) (Φ : HeckeEigensystem F ℂ) :
    IsArithCuspRealizable F pins Φ ↔ Nonempty (SmoothCuspRealizationAt F pins Φ.toRawCentral) :=
  Iff.rfl

theorem isSmoothCuspRealizable_iff_isArithCuspRealizable_ofRawCentral (pins : CarrierPins F)
    (Ψ : HeckeEigensystem F ℂ) :
    IsSmoothCuspRealizable F pins Ψ ↔ IsArithCuspRealizable F pins Ψ.ofRawCentral := by
  unfold IsArithCuspRealizable; rw [HeckeEigensystem.toRawCentral_ofRawCentral]

def IsArithCuspRealizableVia (pins : CarrierPins F) {R : Type*} [CommRing R]
    (ι : R →+* ℂ) (Φ : HeckeEigensystem F R) : Prop :=
  IsArithCuspRealizable F pins (Φ.map ι)

theorem isArithCuspRealizableVia_id (pins : CarrierPins F) (Φ : HeckeEigensystem F ℂ) :
    IsArithCuspRealizableVia F pins (RingHom.id ℂ) Φ ↔ IsArithCuspRealizable F pins Φ := by
  unfold IsArithCuspRealizableVia; rw [HeckeEigensystem.map_id]

def arithCuspNotionOf
    (pins : ∀ (F : Type) [Field F] [NumberField F], CarrierPins F) :
    CuspidalityNotion ℂ where
  IsCusp := fun F _i1 _i2 Φ => @IsArithCuspRealizable F _i1 _i2 (pins F) Φ

theorem arithCuspNotionOf_isCusp_iff
    (pins : ∀ (F : Type) [Field F] [NumberField F], CarrierPins F)
    (Φ : HeckeEigensystem F ℂ) :
    (arithCuspNotionOf pins).IsCusp F Φ ↔ IsArithCuspRealizable F (pins F) Φ := Iff.rfl

variable {F}

theorem IsArithCuspRealizable.congr {pins : CarrierPins F} {Φ Φ' : HeckeEigensystem F ℂ}
    (transport : ∀ Ψ Ψ' : HeckeEigensystem F ℂ, Ψ'.level = Ψ.level →
      HeckeEigensystem.AgreesAwayFromFinite Ψ Ψ' →
        IsSmoothCuspRealizable F pins Ψ → IsSmoothCuspRealizable F pins Ψ')
    (hlev : Φ'.level = Φ.level) (hagree : HeckeEigensystem.AgreesAwayFromFinite Φ Φ')
    (h : IsArithCuspRealizable F pins Φ) : IsArithCuspRealizable F pins Φ' :=
  transport Φ.toRawCentral Φ'.toRawCentral hlev hagree.toRawCentral h

end AutomorphicForm

end
