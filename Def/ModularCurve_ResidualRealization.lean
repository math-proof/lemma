module

public import Def.HeckeGalois_EichlerShimura
public import Def.FLTPrelim_Ramification
public import Instance.EllipticCurve_FrobeniusTrace
public import Mathlib.LinearAlgebra.Determinant

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace ModularCurve


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
