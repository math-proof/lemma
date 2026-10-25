import Def.HeckeGalois_EichlerShimura
import Instance.FLTPrelim_Modularity

set_option autoImplicit false

noncomputable section

namespace ModularCurve

def IsEigenformIdeal (N : ℕ) (𝔪 : Ideal HeckeAlg) : Prop :=
  ∃ (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (_ : f.IsNormalizedEigenform)
    (k : Type) (_ : Field k) (_ : Finite k) (𝒪 : Subring ℂ)
    (h𝒪 : ∀ ℓ : Nat.Primes, ModularFormClass.qCoeff f ℓ ∈ 𝒪) (φ : 𝒪 →+* k),
      𝔪 = eigenIdeal (fun ℓ => φ ⟨ModularFormClass.qCoeff f ℓ, h𝒪 ℓ⟩)

end ModularCurve

end
