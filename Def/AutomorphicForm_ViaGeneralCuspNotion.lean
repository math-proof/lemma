import Def.AutomorphicForm_ViaCompactCuspNotion
import Lemma.AutomorphicForm.ProductionPinsGeneral

set_option autoImplicit false

open IsDedekindDomain NumberField EisensteinWeightOne CongruenceSubgroup

noncomputable section

namespace AutomorphicForm

def viaGeneralCuspNotion : CuspidalityNotion (ℤ√(-2)) where
  IsCusp := fun F _i1 _i2 Φ =>
    (∃ R : SmoothCuspRealizationAt F (productionPinsGeneral F)
        ((Φ.map iotaZsqrtdNegTwo).toRawCentral),
      IsGenuineCuspRealizationAt F (productionPinsGeneral F)
          ((Φ.map iotaZsqrtdNegTwo).toRawCentral) R ∧
      (∀ w : InfinitePlace F, ∀ hw : w.IsReal,
        HasArchCharacterAt₀ F w (archWeightOneAt hw) R.toFun) ∧
      (∀ w : InfinitePlace F, ∀ hw : w.IsReal,
        IsArchHolomorphicAt w hw R.toFun)) ∧
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S,
      Φ.b v = ((chiNegThree (Ideal.absNorm v.asIdeal) : ℤ) : ℤ√(-2))

end AutomorphicForm

end
