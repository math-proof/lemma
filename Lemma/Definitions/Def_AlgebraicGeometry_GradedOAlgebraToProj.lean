import Mathlib
import Lemma.Definitions.Def_AlgebraicGeometry_GradedOAlgebraSectionRing

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory Opposite HomogeneousLocalization

noncomputable section

namespace AlgebraicGeometry.GradedOAlgebra

open AlgebraicGeometry.Scheme.Modules

variable {S : Type u} [CommRing S] {X : Scheme.{u}}

structure IsCanonicalToProj (f : X ⟶ Spec (CommRingCat.of S)) (L : X.Modules)
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)) (θ : X ⟶ Proj 𝓡) : Prop where

  comp_toSpecZero : θ ≫ Proj.toSpecZero 𝓡 ≫
      Spec.map (CommRingCat.ofHom ((GradedRing.projZeroRingHom' 𝓡).comp (algebraMap S R))) = f

  isFrameOn : ∀ (n : ℕ), 0 < n → ∀ σ : 𝓡 n, IsFrameOn (ι n σ) (θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R))

  appLE_awayToSection_smul : ∀ (n : ℕ), 0 < n → ∀ (σ : 𝓡 n) (k : ℕ) (s : 𝓡 (k • n)),
      (θ.appLE (Proj.basicOpen 𝓡 (σ : R)) (θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R)) le_rfl
          (Proj.awayToSection 𝓡 (σ : R) (Away.mk 𝓡 σ.2 k (s : R) s.2))) •
        (L.tensorPow (k • n)).presheaf.map (homOfLE (le_top : θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) ≤ ⊤)).op
          (ι (k • n) ⟨(σ : R) ^ k, SetLike.pow_mem_graded k σ.2⟩)
      = (L.tensorPow (k • n)).presheaf.map (homOfLE (le_top : θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) ≤ ⊤)).op (ι (k • n) s)

end AlgebraicGeometry.GradedOAlgebra

end
