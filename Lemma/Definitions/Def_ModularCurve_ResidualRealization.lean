import Lemma.Definitions.Def_HeckeGalois_EichlerShimura
import Lemma.Definitions.Def_FLTPrelim_Ramification
import Lemma.Definitions.Def_EllipticCurve_FrobeniusTrace
import Mathlib.LinearAlgebra.Determinant

set_option autoImplicit false

noncomputable section

namespace ModularCurve

section ResidualRealization

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (p : ℕ) (J : Type*) [AddCommGroup J] [Module HeckeAlg J]
  [DistribMulAction (L ≃ₐ[K] L) J]
variable (k : Type*) [Field k] (φ : HeckeAlg →+* k)
variable (V : Type*) [AddCommGroup V] [Module k V]
variable (π : J → V) (ρ : (L ≃ₐ[K] L) →* (V ≃ₗ[k] V))

structure IsResidualRealization : Prop where

  finite : Module.Finite k V

  finrank_eq : Module.finrank k V = 2

  map_zero : π 0 = 0

  map_add : ∀ x y : J, p • x = 0 → p • y = 0 → π (x + y) = π x + π y

  map_galois : ∀ (σ : L ≃ₐ[K] L) (x : J), p • x = 0 → π (σ • x) = ρ σ (π x)

  map_hecke : ∀ (t : HeckeAlg) (x : J), p • x = 0 → π (t • x) = φ t • π x

  spanning : Submodule.span k (π '' {x : J | p • x = 0}) = ⊤

end ResidualRealization

section Determinant

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

def CyclotomicDeterminant (N p : ℕ) (ρ : (L ≃ₐ[K] L) →* (V ≃ₗ[k] V)) : Prop :=
  ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N * p →
    ∀ A : ValuationSubring L, A.LiesOverPrime ℓ →
      ∀ σ : L ≃ₐ[K] L, A.IsFrobeniusAt σ ℓ →
        LinearMap.det (ρ σ).toLinearMap = (ℓ : k)

end Determinant

end ModularCurve

end
