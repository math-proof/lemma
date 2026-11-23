import Lemma.Ideal.SmoothCuspRealization

set_option autoImplicit false

open IsDedekindDomain NumberField

noncomputable section

namespace AutomorphicForm

namespace HeckeEigensystem

variable {F : Type*} [Field F] [NumberField F]

def cNorm (v : HeightOneSpectrum (𝓞 F)) : ℂ := (Ideal.absNorm v.asIdeal : ℂ)

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

end HeckeEigensystem

variable (F : Type) [Field F] [NumberField F]

def IsArithCuspRealizable (pins : CarrierPins F) (Φ : HeckeEigensystem F ℂ) : Prop :=
  IsSmoothCuspRealizable F pins Φ.toRawCentral

def IsArithCuspRealizableVia (pins : CarrierPins F) {R : Type*} [CommRing R]
    (ι : R →+* ℂ) (Φ : HeckeEigensystem F R) : Prop :=
  IsArithCuspRealizable F pins (Φ.map ι)

def arithCuspNotionOf
    (pins : ∀ (F : Type) [Field F] [NumberField F], CarrierPins F) :
    CuspidalityNotion ℂ where
  IsCusp := fun F _i1 _i2 Φ => @IsArithCuspRealizable F _i1 _i2 (pins F) Φ

variable {F}

end AutomorphicForm

end
