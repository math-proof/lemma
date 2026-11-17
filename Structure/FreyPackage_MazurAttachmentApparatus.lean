module

public import Mathlib
public import Structure.FLTPrelim_FreyPackage
public import Def.FreyPackage_LevelRaising
public import Instance.FreyPackage_GaloisRep
public import Def.GaloisRep_GlobalUnramifiedAt
public import Lemma.MvPolynomial.HeckeModule
public import Def.ModularCurve_HeckeInputsAll
public import Structure.ModularCurve_MazurPrincipleCore

set_option autoImplicit false

public noncomputable section

namespace FreyPackage

open ModularCurve
open scoped CongruenceSubgroup


structure EigenformIdealData (P : FreyPackage) (M : ℕ) (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2)
    (𝔪 : Ideal HeckeAlg) : Prop where
  hmax : 𝔪.IsMaximal
  hpmem : ((P.p : ℕ) : HeckeAlg) ∈ 𝔪
  heis : ¬ IsEventuallyEisenstein 𝔪
  heigen : ∀ (ℓ : Nat.Primes) (b : ℤ), (algebraMap ℤ ℂ b = ModularFormClass.qCoeff g ℓ) →
    heckeGen ℓ - MvPolynomial.C b ∈ 𝔪


end FreyPackage

end
