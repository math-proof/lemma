import Def.HeckeGalois_EichlerShimura
import Instance.FLTPrelim_Modularity
import Def.FreyPackage_LevelRaising

namespace ModularCurve

def IsTwoNewEigenformIdeal (M q q' : ℕ) (𝔪 : Ideal HeckeAlg) : Prop :=
  ∃ (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (_ : f.IsNormalizedEigenform)
    (_ : f.IsNewAt q) (_ : f.IsNewAt q')
    (k : Type) (_ : Field k) (_ : Finite k) (𝒪 : Subring ℂ)
    (h𝒪 : ∀ ℓ : Nat.Primes, ModularFormClass.qCoeff f ℓ ∈ 𝒪) (φ : 𝒪 →+* k),
      𝔪 = eigenIdeal (fun ℓ => φ ⟨ModularFormClass.qCoeff f ℓ, h𝒪 ℓ⟩)

def TwoNewEigensystemsFactor (M q q' : ℕ) (Y : Type*) [AddCommGroup Y] [Module HeckeAlg Y] :
    Prop :=
  ∀ (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2), f.IsNormalizedEigenform →
    f.IsNewAt q → f.IsNewAt q' →
      Module.annihilator HeckeAlg Y ≤
        RingHom.ker (MvPolynomial.aeval (R := ℤ)
          (fun ℓ : Nat.Primes => ModularFormClass.qCoeff f ℓ))

end ModularCurve
