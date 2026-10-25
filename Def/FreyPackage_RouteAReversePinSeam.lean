import Lemma.FLTPrelim.FreyPackage
import Instance.FLTPrelim_GaloisRep
import Instance.FLTPrelim_Modularity
import Def.FLTPrelim_ModularRep
import Def.FreyPackage_LevelRaising
import Def.FLTPrelim_Ramification

set_option autoImplicit false

set_option maxHeartbeats 600000

open WeierstrassCurve WeierstrassCurve.Affine.Point CuspForm

open scoped CongruenceSubgroup

namespace FreyPackage

def FreyCurveApOfModelThreeAgreement (P : FreyPackage) : Prop :=
  ∀ W : WeierstrassCurve ℤ, W.IsIntegralModelOf P.freyCurve →
    W.IsGoodPrimeFor 3 → W.apOfModel 3 = 0

def RouteAReversePinBadOnlySeam (P : FreyPackage) : Prop :=
  ∀ (N : ℕ) (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (W : WeierstrassCurve ℤ)
    (𝔪 : Ideal (integralClosure ℤ ℂ)), P.IsCongruentWitness N f W 𝔪 →
    ∀ ℓ : ℕ, ℓ.Prime → (freyCurveInt P).IsGoodPrimeFor ℓ → ¬ ℓ ∣ N → ℓ ≠ P.p →
      ¬ W.IsGoodPrimeFor ℓ →
      ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff f ℓ ∧
        a - (((freyCurveInt P).apOfModel ℓ : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪

end FreyPackage
