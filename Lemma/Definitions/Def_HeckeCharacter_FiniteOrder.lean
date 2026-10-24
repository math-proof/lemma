import Lemma.Definitions.Def_AutomorphicForm_AdelicLsXi

set_option autoImplicit false

open NumberField AutomorphicForm IsDedekindDomain WithZero

noncomputable section

namespace HeckeCharacter

variable (K : Type*) [Field K] [NumberField K]

structure IsFiniteOrderHeckeChar (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) : Prop where
  isIdeleClassChar : IsIdeleClassChar (𝓞 K) K χ
  continuous : Continuous χ
  isOfFinOrder : IsOfFinOrder χ

def idealMultiplicity (v : HeightOneSpectrum (𝓞 K)) (𝔣 : Ideal (𝓞 K)) : ℕ :=
  (Associates.mk v.asIdeal).count (Associates.mk 𝔣).factors

def AdmitsModulus (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (𝔣 : Ideal (𝓞 K)) : Prop :=
  ∀ u : (AdeleRing (𝓞 K) K)ˣ,
    (u : AdeleRing (𝓞 K) K).1 = 1 →
    (∀ v : HeightOneSpectrum (𝓞 K),
      Valued.v ((u : AdeleRing (𝓞 K) K).2 v) = 1 ∧
      Valued.v ((u : AdeleRing (𝓞 K) K).2 v - 1)
        ≤ WithZero.exp (-(idealMultiplicity K v 𝔣 : ℤ))) →
    χ u = 1

end HeckeCharacter
