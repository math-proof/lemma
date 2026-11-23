module

public import Theorem.Ideal.SmoothCuspRealization

public noncomputable section

set_option autoImplicit false

open IsDedekindDomain NumberField

noncomputable section

namespace AutomorphicForm

namespace HeckeEigensystem

variable {F : Type*} [Field F] [NumberField F]


public theorem cNorm_ne_zero (v : HeightOneSpectrum (𝓞 F)) : cNorm v ≠ 0 := by
  have hN : Ideal.absNorm v.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
  rw [cNorm, Ne, Nat.cast_eq_zero]
  exact hN


@[simp] public theorem toRawCentral_level (Φ : HeckeEigensystem F ℂ) : Φ.toRawCentral.level = Φ.level := rfl

@[simp] public theorem toRawCentral_a (Φ : HeckeEigensystem F ℂ) (v : HeightOneSpectrum (𝓞 F)) :
    Φ.toRawCentral.a v = Φ.a v := rfl

@[simp] public theorem toRawCentral_b (Φ : HeckeEigensystem F ℂ) (v : HeightOneSpectrum (𝓞 F)) :
    Φ.toRawCentral.b v = (cNorm v)⁻¹ * Φ.b v := rfl

@[simp] public theorem ofRawCentral_level (Ψ : HeckeEigensystem F ℂ) : Ψ.ofRawCentral.level = Ψ.level := rfl

@[simp] public theorem ofRawCentral_a (Ψ : HeckeEigensystem F ℂ) (v : HeightOneSpectrum (𝓞 F)) :
    Ψ.ofRawCentral.a v = Ψ.a v := rfl

@[simp] public theorem ofRawCentral_b (Ψ : HeckeEigensystem F ℂ) (v : HeightOneSpectrum (𝓞 F)) :
    Ψ.ofRawCentral.b v = cNorm v * Ψ.b v := rfl


@[simp] public theorem ofRawCentral_toRawCentral (Φ : HeckeEigensystem F ℂ) :
    Φ.toRawCentral.ofRawCentral = Φ := by
  cases Φ with
  | mk level hl a b =>
    simp only [toRawCentral, ofRawCentral, mk.injEq, true_and]
    funext v
    rw [← mul_assoc, mul_inv_cancel₀ (cNorm_ne_zero v), one_mul]


@[simp] public theorem toRawCentral_ofRawCentral (Ψ : HeckeEigensystem F ℂ) :
    Ψ.ofRawCentral.toRawCentral = Ψ := by
  cases Ψ with
  | mk level hl a b =>
    simp only [toRawCentral, ofRawCentral, mk.injEq, true_and]
    funext v
    rw [← mul_assoc, inv_mul_cancel₀ (cNorm_ne_zero v), one_mul]


public theorem toRawCentral_injective : Function.Injective (toRawCentral (F := F)) := fun Φ Φ' h => by
  rw [← ofRawCentral_toRawCentral Φ, h, ofRawCentral_toRawCentral]


public theorem AgreesAwayFromFinite.toRawCentral {Φ Φ' : HeckeEigensystem F ℂ}
    (h : AgreesAwayFromFinite Φ Φ') : AgreesAwayFromFinite Φ.toRawCentral Φ'.toRawCentral := by
  obtain ⟨S, hS⟩ := h
  exact ⟨S, fun v hv => ⟨(hS v hv).1, congrArg ((cNorm v)⁻¹ * ·) (hS v hv).2⟩⟩


public theorem AgreesAwayFromFinite.of_toRawCentral {Φ Φ' : HeckeEigensystem F ℂ}
    (h : AgreesAwayFromFinite Φ.toRawCentral Φ'.toRawCentral) : AgreesAwayFromFinite Φ Φ' := by
  obtain ⟨S, hS⟩ := h
  exact ⟨S, fun v hv =>
    ⟨(hS v hv).1, mul_left_cancel₀ (inv_ne_zero (cNorm_ne_zero v)) (hS v hv).2⟩⟩

end HeckeEigensystem

variable (F : Type) [Field F] [NumberField F]


public theorem isArithCuspRealizable_iff (pins : CarrierPins F) (Φ : HeckeEigensystem F ℂ) :
    IsArithCuspRealizable F pins Φ ↔ Nonempty (SmoothCuspRealizationAt F pins Φ.toRawCentral) :=
  Iff.rfl


public theorem isSmoothCuspRealizable_iff_isArithCuspRealizable_ofRawCentral (pins : CarrierPins F)
    (Ψ : HeckeEigensystem F ℂ) :
    IsSmoothCuspRealizable F pins Ψ ↔ IsArithCuspRealizable F pins Ψ.ofRawCentral := by
  unfold IsArithCuspRealizable; rw [HeckeEigensystem.toRawCentral_ofRawCentral]


public theorem isArithCuspRealizableVia_id (pins : CarrierPins F) (Φ : HeckeEigensystem F ℂ) :
    IsArithCuspRealizableVia F pins (RingHom.id ℂ) Φ ↔ IsArithCuspRealizable F pins Φ := by
  unfold IsArithCuspRealizableVia; rw [HeckeEigensystem.map_id]


public theorem arithCuspNotionOf_isCusp_iff
    (pins : ∀ (F : Type) [Field F] [NumberField F], CarrierPins F)
    (Φ : HeckeEigensystem F ℂ) :
    (arithCuspNotionOf pins).IsCusp F Φ ↔ IsArithCuspRealizable F (pins F) Φ := Iff.rfl

variable {F}


public theorem IsArithCuspRealizable.congr {pins : CarrierPins F} {Φ Φ' : HeckeEigensystem F ℂ}
    (transport : ∀ Ψ Ψ' : HeckeEigensystem F ℂ, Ψ'.level = Ψ.level →
      HeckeEigensystem.AgreesAwayFromFinite Ψ Ψ' →
        IsSmoothCuspRealizable F pins Ψ → IsSmoothCuspRealizable F pins Ψ')
    (hlev : Φ'.level = Φ.level) (hagree : HeckeEigensystem.AgreesAwayFromFinite Φ Φ')
    (h : IsArithCuspRealizable F pins Φ) : IsArithCuspRealizable F pins Φ' :=
  transport Φ.toRawCentral Φ'.toRawCentral hlev hagree.toRawCentral h

end AutomorphicForm

end
