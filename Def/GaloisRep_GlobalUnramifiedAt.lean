import Def.FLTPrelim_Ramification

set_option autoImplicit false

namespace GlobalGaloisRep

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

def IsUnramifiedAt {G : Type*} [Monoid G] (ρ : (L ≃ₐ[K] L) →* G) (q : ℕ) : Prop :=
  ∀ A : ValuationSubring L, A.LiesOverPrime q → A.inertiaSubgroupIn K ≤ ρ.ker

end GlobalGaloisRep
