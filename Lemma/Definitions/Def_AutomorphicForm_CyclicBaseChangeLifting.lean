import Lemma.Definitions.Def_AutomorphicForm_HeckeEigensystem
import Lemma.Definitions.Def_LanglandsTunnell_ArtinCoreCTM

open IsDedekindDomain NumberField
open Deep.NTSupply LanglandsTunnell.P2.Artin

noncomputable section

namespace AutomorphicForm.CyclicBaseChangeLifting

section GlobalLifting

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E]

structure LanglandsLiftingProperties (notion : CuspidalityNotion ℂ) : Prop where

  propertyA : ∀ π : HeckeEigensystem F ℂ, notion.IsCusp F π →
    ∃ Ψ : HeckeEigensystem E ℂ, IsBaseChangeOf π Ψ

  propertyB : ∀ Ψ : HeckeEigensystem E ℂ, notion.IsCusp E Ψ →
    Ψ.IsConstantOnFibers F →
    ∃ π : HeckeEigensystem F ℂ, notion.IsCusp F π ∧ IsBaseChangeOf π Ψ

  propertyC : ∀ π π' : HeckeEigensystem F ℂ, notion.IsCusp F π → notion.IsCusp F π' →
    ∀ Ψ : HeckeEigensystem E ℂ, IsBaseChangeOf π Ψ → IsBaseChangeOf π' Ψ →
    ∃ 𝔣 : Ideal (𝓞 F), IsAdmissibleModulus F E 𝔣 ∧
      ∃ ω : NarrowRayClassGroup F 𝔣 →* ℂˣ,
        (∀ (w : HeightOneSpectrum (𝓞 E)) (hw : ¬ ((w.under (𝓞 F)).asIdeal ∣ 𝔣)),
          ω (primeClass F 𝔣 (w.under (𝓞 F)) hw ^
            ((w.under (𝓞 F)).asIdeal.inertiaDeg' w.asIdeal)) = 1) ∧
        ∃ S : Finset (HeightOneSpectrum (𝓞 F)),
          ∀ v ∉ S, ∀ (hv : ¬ v.asIdeal ∣ 𝔣),
            π'.a v = (ω (primeClass F 𝔣 v hv) : ℂ) * π.a v ∧
            π'.b v = (ω (primeClass F 𝔣 v hv) : ℂ) ^ 2 * π.b v

  propertyG : ∀ (π : HeckeEigensystem F ℂ) (Ψ : HeckeEigensystem E ℂ),
    IsBaseChangeOf π Ψ →
    ∃ S : Finset (HeightOneSpectrum (𝓞 E)),
      ∀ w ∉ S, IsBaseChangeAt π Ψ w

end GlobalLifting

end AutomorphicForm.CyclicBaseChangeLifting
