import Structure.GaloisRep_Adic
import Instance.CuspForm_HeckeAlgebra

open Polynomial

namespace CuspForm

structure HeckeGaloisRepDatum (N : ℕ) [NeZero N] (S : Set ℕ)
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    (θ : heckeAlgebra N 2 S →+* IsLocalRing.ResidueField 𝒪)
    (T : Type) [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T] [Algebra 𝒪 T] [IsLocalHom (algebraMap 𝒪 T)]
    [Module.Finite 𝒪 T] [Module.Free 𝒪 T] : Type 1 where

  π : heckeAlgebra N 2 S →+* T

  residue_π : ∀ t : heckeAlgebra N 2 S,
    IsLocalRing.residue T (π t) = IsLocalRing.ResidueField.map (algebraMap 𝒪 T) (θ t)

  adjoin_range_π : Algebra.adjoin 𝒪 (Set.range π) = ⊤

  exists_point : ∀ χ : heckeAlgebra N 2 S →+* 𝒪,
    (∀ t : heckeAlgebra N 2 S, IsLocalRing.residue 𝒪 (χ t) = θ t) →
      ∃ ψ : T →ₐ[𝒪] 𝒪, ∀ t : heckeAlgebra N 2 S, ψ (π t) = χ t

  residue_surjective : Function.Surjective (IsLocalRing.residue T ∘ algebraMap 𝒪 T)

  ρ : GaloisRepAdic T

  charpoly_frob : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S),
    ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
        LinearMap.charpoly (ρ.ρ σ) = X ^ 2 - C (π (heckeAlgebra.T hℓ hℓN hℓS)) * X + C ((ℓ : T))

  residual_absIrr : ρ.residual.IsAbsolutelyIrreducible

end CuspForm
