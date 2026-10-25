import Def.ModularCurve_ResidualRealization
import Lemma.ModularCurve.ArithmeticGalois
import Lemma.FLTPrelim.ModularRep
import Def.FreyPackage_EigenformRealizationSupplyField

set_option autoImplicit false

open Module LinearMap CongruenceSubgroup
open ModularCurve
open WeierstrassCurve WeierstrassCurve.Affine.Point
open scoped WeierstrassCurve.Affine

namespace FreyPackage


theorem eigenformRealizationSupplyFieldAt_iff_eSMasterAttachmentSupplyField
    {P : FreyPackage} {M : ℕ} [Module HeckeAlg (JZero M)] :
    P.EigenformRealizationSupplyFieldAt M ↔ ESMasterAttachmentSupplyField P M (JZero M) :=
  Iff.rfl

end FreyPackage
