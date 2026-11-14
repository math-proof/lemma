-- Carved from Lemma/Definitions/Def_FreyPackage_ExchangeCase.lean: instance decls only.
import Lemma.WeierstrassCurve.FreyPackage
import Instance.FLTPrelim_GaloisRep
import Lemma.CuspForm.ModularRep
import Instance.FLTPrelim_Modularity
import Def.FLTPrelim_Ramification
import Instance.FreyPackage_GaloisRep
import Def.FreyPackage_LevelRaising
import Lemma.ValuationSubring.GlobalUnramifiedAt

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine.Point

open scoped CongruenceSubgroup

namespace FreyPackage

noncomputable local instance instDecEqQbarExchangeCase :
    DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _

instance (P : FreyPackage) (q : ℕ) : Decidable (P.ExchangeCongruence q) :=
  Int.decidableDvd _ _

end FreyPackage
