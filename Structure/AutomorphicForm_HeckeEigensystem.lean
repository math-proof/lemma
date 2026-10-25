import Mathlib

open IsDedekindDomain NumberField

noncomputable section

namespace AutomorphicForm

structure HeckeEigensystem (F : Type*) [Field F] [NumberField F]
    (R : Type*) [CommRing R] where

  level : Ideal (𝓞 F)

  level_ne_bot : level ≠ ⊥

  a : HeightOneSpectrum (𝓞 F) → R

  b : HeightOneSpectrum (𝓞 F) → R

namespace HeckeEigensystem

variable {F : Type*} [Field F] [NumberField F] {R : Type*} [CommRing R]


def AgreesAwayFromFinite (Φ Φ' : HeckeEigensystem F R) : Prop :=
  ∃ S : Finset (HeightOneSpectrum (𝓞 F)),
    ∀ v ∉ S, Φ.a v = Φ'.a v ∧ Φ.b v = Φ'.b v

def IsConstantOnFibers {L : Type*} [Field L] [NumberField L]
    {R : Type*} [CommRing R] (Φ : HeckeEigensystem L R)
    (E : Type*) [Field E] [NumberField E]
    [Algebra (𝓞 E) (𝓞 L)] [Algebra.IsIntegral (𝓞 E) (𝓞 L)] : Prop :=
  ∃ S : Finset (HeightOneSpectrum (𝓞 L)),
    ∀ 𝔓₁ ∉ S, ∀ 𝔓₂ ∉ S,
      𝔓₁.under (𝓞 E) = 𝔓₂.under (𝓞 E) →
      (𝔓₁.under (𝓞 E)).asIdeal.inertiaDeg' 𝔓₁.asIdeal
        = (𝔓₂.under (𝓞 E)).asIdeal.inertiaDeg' 𝔓₂.asIdeal →
      Φ.a 𝔓₁ = Φ.a 𝔓₂ ∧ Φ.b 𝔓₁ = Φ.b 𝔓₂

end HeckeEigensystem

def satakePow {R : Type*} [CommRing R] (n : ℕ) (s e : R) : R :=
  match n with
  | 0 => 2
  | 1 => s
  | (n + 2) => s * satakePow (n + 1) s e - e * satakePow n s e


section Transfer

variable {E L : Type*} [Field E] [NumberField E] [Field L] [NumberField L]
  [Algebra (𝓞 E) (𝓞 L)] [Algebra.IsIntegral (𝓞 E) (𝓞 L)]
  {R : Type*} [CommRing R]

def IsBaseChangeAt (π : HeckeEigensystem E R) (Φ : HeckeEigensystem L R)
    (𝔓 : HeightOneSpectrum (𝓞 L)) : Prop :=
  Φ.a 𝔓 = satakePow ((𝔓.under (𝓞 E)).asIdeal.inertiaDeg' 𝔓.asIdeal)
            (π.a (𝔓.under (𝓞 E))) (π.b (𝔓.under (𝓞 E))) ∧
  Φ.b 𝔓 = (π.b (𝔓.under (𝓞 E))) ^ ((𝔓.under (𝓞 E)).asIdeal.inertiaDeg' 𝔓.asIdeal)

def IsBaseChangeOf (π : HeckeEigensystem E R) (Φ : HeckeEigensystem L R) : Prop :=
  ∃ S : Finset (HeightOneSpectrum (𝓞 L)), ∀ 𝔓 ∉ S, IsBaseChangeAt π Φ 𝔓


end Transfer

structure CuspidalityNotion (R : Type*) [CommRing R] where

  IsCusp : ∀ (F : Type) [Field F] [NumberField F], HeckeEigensystem F R → Prop

structure DescentPackage (R : Type*) [CommRing R]
    (E L : Type) [Field E] [NumberField E] [Field L] [NumberField L]
    [Algebra (𝓞 E) (𝓞 L)] [Algebra.IsIntegral (𝓞 E) (𝓞 L)]
    (Φ₀ : HeckeEigensystem L R) where

  notion : CuspidalityNotion R

  seed_isCusp : notion.IsCusp L Φ₀

  seed_constantOnFibers : Φ₀.IsConstantOnFibers E

  descent : ∀ Φ : HeckeEigensystem L R, notion.IsCusp L Φ → Φ.IsConstantOnFibers E →
    ∃ π : HeckeEigensystem E R, notion.IsCusp E π ∧ IsBaseChangeOf π Φ

  multOne : ∀ π π' : HeckeEigensystem E R, notion.IsCusp E π → notion.IsCusp E π' →
    HeckeEigensystem.AgreesAwayFromFinite π π' →
    ∀ v : HeightOneSpectrum (𝓞 E), ¬ v.asIdeal ∣ π.level → ¬ v.asIdeal ∣ π'.level →
      π.a v = π'.a v

end AutomorphicForm

end
