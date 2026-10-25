import Mathlib
import Structure.GaloisRep_Adic

set_option autoImplicit false

noncomputable section

namespace GaloisRep

open IsLocalRing

variable (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]

structure IsArtinianTestAlgebra (A : Type) [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] : Prop where
  isLocalHom : IsLocalHom (algebraMap 𝒪 A)
  residue_surjective : Function.Surjective (IsLocalRing.residue A ∘ algebraMap 𝒪 A)
  isArtinian : IsArtinianRing A

structure IsDeformationCondition
    (𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop) :
    Prop where

  of_isEquiv : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A],
    IsArtinianTestAlgebra 𝒪 A → ∀ ⦃ρ ρ' : GaloisRepAdic A⦄, ρ.IsEquiv ρ' → 𝒟 ρ → 𝒟 ρ'

  baseChangeAlong : ∀ ⦃A B : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A]
    [CommRing B] [IsLocalRing B] [Algebra 𝒪 B],
    IsArtinianTestAlgebra 𝒪 A → IsArtinianTestAlgebra 𝒪 B →
    ∀ (φ : A →ₐ[𝒪] B) (hφ : IsLocalHom (φ : A →+* B)) ⦃ρ : GaloisRepAdic A⦄,
      𝒟 ρ → 𝒟 (ρ.baseChangeAlong (φ : A →+* B) hφ)

  of_baseChangeAlong_injective : ∀ ⦃A B : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A]
    [CommRing B] [IsLocalRing B] [Algebra 𝒪 B],
    IsArtinianTestAlgebra 𝒪 A → IsArtinianTestAlgebra 𝒪 B →
    ∀ (φ : A →ₐ[𝒪] B) (hφ : IsLocalHom (φ : A →+* B)), Function.Injective φ →
      ∀ ⦃ρ : GaloisRepAdic A⦄, 𝒟 (ρ.baseChangeAlong (φ : A →+* B) hφ) → 𝒟 ρ

  of_fibreProduct : ∀ ⦃A B C P : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A]
    [CommRing B] [IsLocalRing B] [Algebra 𝒪 B] [CommRing C] [IsLocalRing C] [Algebra 𝒪 C]
    [CommRing P] [IsLocalRing P] [Algebra 𝒪 P],
    IsArtinianTestAlgebra 𝒪 A → IsArtinianTestAlgebra 𝒪 B → IsArtinianTestAlgebra 𝒪 C →
    IsArtinianTestAlgebra 𝒪 P →
    ∀ (f : A →ₐ[𝒪] C) (g : B →ₐ[𝒪] C) (pA : P →ₐ[𝒪] A) (pB : P →ₐ[𝒪] B)
      (hpA : IsLocalHom (pA : P →+* A)) (hpB : IsLocalHom (pB : P →+* B)),
      f.comp pA = g.comp pB →
      Function.Injective (fun x => (pA x, pB x)) →
      (∀ a b, f a = g b → ∃ x, pA x = a ∧ pB x = b) →
      ∀ ⦃ρ : GaloisRepAdic P⦄,
        𝒟 (ρ.baseChangeAlong (pA : P →+* A) hpA) → 𝒟 (ρ.baseChangeAlong (pB : P →+* B) hpB) → 𝒟 ρ

  iff_forall_surjective : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (maximalIdeal A) A] [Algebra 𝒪 A],
    IsLocalHom (algebraMap 𝒪 A) → Function.Surjective (IsLocalRing.residue A ∘ algebraMap 𝒪 A) →
    ∀ (ρ : GaloisRepAdic A),
      𝒟 ρ ↔ ∀ ⦃B : Type⦄ [CommRing B] [IsLocalRing B] [Algebra 𝒪 B], IsArtinianTestAlgebra 𝒪 B →
        ∀ (q : A →ₐ[𝒪] B) (hq : IsLocalHom (q : A →+* B)), Function.Surjective q →
          𝒟 (ρ.baseChangeAlong (q : A →+* B) hq)

end GaloisRep
end
