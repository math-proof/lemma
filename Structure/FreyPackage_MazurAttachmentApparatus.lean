import Mathlib
import Structure.FLTPrelim_FreyPackage
import Def.FreyPackage_LevelRaising
import Instance.FreyPackage_GaloisRep
import Def.GaloisRep_GlobalUnramifiedAt
import Lemma.ModularCurve.HeckeModule
import Def.ModularCurve_HeckeInputsAll
import Structure.ModularCurve_MazurPrincipleCore

set_option autoImplicit false

noncomputable section

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
