import Mathlib
import Lemma.Definitions.Def_AutomorphicForm_HeckeEigensystem

open IsDedekindDomain NumberField AutomorphicForm

noncomputable section

namespace AutomorphicForm

section FormalLift

variable (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
  [Algebra (𝓞 F) (𝓞 K)] [Algebra.IsIntegral (𝓞 F) (𝓞 K)]
  {R : Type*} [CommRing R]

def formalBaseChange (π : HeckeEigensystem F R) : HeckeEigensystem K R where
  level := ⊤
  level_ne_bot := by simp
  a := fun 𝔓 => satakePow ((𝔓.under (𝓞 F)).asIdeal.inertiaDeg' 𝔓.asIdeal)
    (π.a (𝔓.under (𝓞 F))) (π.b (𝔓.under (𝓞 F)))
  b := fun 𝔓 => (π.b (𝔓.under (𝓞 F))) ^
    ((𝔓.under (𝓞 F)).asIdeal.inertiaDeg' 𝔓.asIdeal)

@[simp] theorem formalBaseChange_a (π : HeckeEigensystem F R)
    (𝔓 : HeightOneSpectrum (𝓞 K)) :
    (formalBaseChange F K π).a 𝔓 =
      satakePow ((𝔓.under (𝓞 F)).asIdeal.inertiaDeg' 𝔓.asIdeal)
        (π.a (𝔓.under (𝓞 F))) (π.b (𝔓.under (𝓞 F))) := rfl

@[simp] theorem formalBaseChange_b (π : HeckeEigensystem F R)
    (𝔓 : HeightOneSpectrum (𝓞 K)) :
    (formalBaseChange F K π).b 𝔓 =
      (π.b (𝔓.under (𝓞 F))) ^ ((𝔓.under (𝓞 F)).asIdeal.inertiaDeg' 𝔓.asIdeal) := rfl

end FormalLift

section CubicHypothesis

variable (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
  [Algebra (𝓞 F) (𝓞 K)] [Algebra.IsIntegral (𝓞 F) (𝓞 K)]

def CubicResidueDegOutside (S : Finset (HeightOneSpectrum (𝓞 K))) : Prop :=
  ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓 ∉ S →
    (𝔓.under (𝓞 F)).asIdeal.inertiaDeg' 𝔓.asIdeal = 1 ∨
    (𝔓.under (𝓞 F)).asIdeal.inertiaDeg' 𝔓.asIdeal = 3

def IsDegreeThreeOutside (S : Finset (HeightOneSpectrum (𝓞 K))) : Prop :=
  ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓 ∉ S →
    (𝔓.under (𝓞 F)).asIdeal.inertiaDeg' 𝔓.asIdeal ≤ 3

end CubicHypothesis

section Package

variable (R : Type*) [CommRing R]
  (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
  [Algebra (𝓞 F) (𝓞 K)] [Algebra.IsIntegral (𝓞 F) (𝓞 K)]

structure JPSSCubicLiftPackage where

  notion : CuspidalityNotion R

  cubicDeg : ∃ S : Finset (HeightOneSpectrum (𝓞 K)), IsDegreeThreeOutside F K S

  lift_automorphic : ∀ π : HeckeEigensystem F R, notion.IsCusp F π →
    ∃ Φ : HeckeEigensystem K R, IsBaseChangeOf π Φ ∧
      (notion.IsCusp K Φ ∨ Φ.IsConstantOnFibers F)

end Package

end AutomorphicForm

end
