module

public import Def.FLTPrelim_Ramification
public import Def.GaloisRep_GlobalUnramifiedAt

public section

set_option autoImplicit false

namespace GlobalGaloisRep

variable {K L : Type*} [Field K] [Field L] [Algebra K L]


public theorem isUnramifiedAt_iff {G : Type*} [Monoid G] {ρ : (L ≃ₐ[K] L) →* G} {q : ℕ} :
    IsUnramifiedAt ρ q ↔
      ∀ A : ValuationSubring L, A.LiesOverPrime q →
        ∀ σ : L ≃ₐ[K] L, σ ∈ A.inertiaSubgroupIn K → ρ σ = 1 :=
  Iff.rfl

end GlobalGaloisRep
