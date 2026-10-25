import Structure.HeckeGalois_EichlerShimura
import Instance.ModularCurve_SpecializationWitness

set_option autoImplicit false

noncomputable section

namespace ModularCurve

section Family

variable (J' : Type*) [AddCommGroup J']

structure CommutingHeckeFamily : Type _ where

  T : Nat.Primes → Module.End ℤ J'

  comm : ∀ q q' : Nat.Primes, Commute (T q) (T q')

variable {J'}

namespace CommutingHeckeFamily

variable (fam : CommutingHeckeFamily J')


end CommutingHeckeFamily

end Family

section Packaging

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (p : ℕ) (J : Type*) [AddCommGroup J] [Module HeckeAlg J]
  [DistribMulAction (L ≃ₐ[K] L) J]

structure SpecializationWitnessData (A : ValuationSubring L) (ℓ : ℕ) (hℓ : ℓ.Prime) :
    Type _ where

  J' : Type

  [addCommGroup : AddCommGroup J']

  fam : CommutingHeckeFamily J'

  sp : J →+ J'

  F : J' →+ J'

  hecke_comm_gen : ∀ (q : Nat.Primes) (x : J), sp (heckeGen q • x) = fam.T q (sp x)

  inertia_comm : ∀ σ ∈ A.inertiaSubgroupIn K, ∀ x : J, sp (σ • x) = sp x

  frobenius_comm : ∀ σ : L ≃ₐ[K] L, A.IsFrobeniusAt σ ℓ → ∀ x : J, sp (σ • x) = F (sp x)

  injective_torsion : ∀ x : J, (∃ n : ℕ, p ^ n • x = 0) → sp x = 0 → x = 0

  relation : ∀ y : J', F (F y) - fam.T ⟨ℓ, hℓ⟩ (F y) + ℓ • y = 0

attribute [instance] SpecializationWitnessData.addCommGroup

end Packaging

end ModularCurve
