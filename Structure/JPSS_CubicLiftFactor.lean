import Mathlib
import Structure.AutomorphicForm_FormalBaseChange
import Def.AutomorphicForm_LocalLFactor
import Theorems.Thm_AutomorphicForm_isBaseChangeOf_formalBaseChange

set_option autoImplicit false

open IsDedekindDomain NumberField Polynomial

noncomputable section

namespace AutomorphicForm

variable {R : Type*} [CommRing R]


section Factor

variable (R : Type*) [CommRing R]
  (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
  [Algebra (𝓞 F) (𝓞 K)] [Algebra.IsIntegral (𝓞 F) (𝓞 K)]

structure JPSSConverseFactored where

  notion : CuspidalityNotion R

  cubicDeg : ∃ S : Finset (HeightOneSpectrum (𝓞 K)), IsDegreeThreeOutside F K S

  ConverseHyp : HeckeEigensystem K R → Prop

  jl_converse : ∀ Φ : HeckeEigensystem K R, ConverseHyp Φ →
    notion.IsCusp K Φ ∨ Φ.IsConstantOnFibers F

  formalLift_converseHyp : ∀ π : HeckeEigensystem F R, notion.IsCusp F π →
    ConverseHyp (formalBaseChange F K π)

variable {R F K}


variable (R F K)

structure JPSSGL3Factored extends JPSSConverseFactored R F K where

  IsGL3Automorphic : (HeightOneSpectrum (𝓞 F) → R × R × R) → Prop

  RankinNice : HeckeEigensystem F R → (HeightOneSpectrum (𝓞 F) → R × R × R) → Prop

  IsIrreducibleInduced : (HeightOneSpectrum (𝓞 K) → R) → Prop

  gl3_induction : ∀ χ : HeightOneSpectrum (𝓞 K) → R, IsIrreducibleInduced χ →
    ∃ σ : HeightOneSpectrum (𝓞 F) → R × R × R, IsGL3Automorphic σ

  rankin_nice : ∀ π : HeckeEigensystem F R, notion.IsCusp F π →
    ∀ σ, IsGL3Automorphic σ → RankinNice π σ

  euler_compare : ∀ π : HeckeEigensystem F R,
    (∀ χ : HeightOneSpectrum (𝓞 K) → R, IsIrreducibleInduced χ →
        ∃ σ, IsGL3Automorphic σ ∧ RankinNice π σ) →
    ConverseHyp (formalBaseChange F K π)

  formalLift_converseHyp_eq : ∀ π hπ,
    formalLift_converseHyp π hπ =
      euler_compare π (fun χ hirr =>
        let ⟨σ, hσ⟩ := gl3_induction χ hirr; ⟨σ, hσ, rankin_nice π hπ σ hσ⟩)

variable {R F K}


end Factor


section SAT

variable (R : Type*) [CommRing R]
  (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
  [Algebra (𝓞 F) (𝓞 K)] [Algebra.IsIntegral (𝓞 F) (𝓞 K)]


end SAT

end AutomorphicForm

end
