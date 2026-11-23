-- Carved from Lemma/Definitions/Def_FreyPackage_ExchangeCase.lean: instance decls only.
module

public import Theorem.WeierstrassCurve.FreyPackage
public import Instance.FLTPrelim_GaloisRep
public import Theorem.CuspForm.ModularRep
public import Instance.FLTPrelim_Modularity
public import Def.FLTPrelim_Ramification
public import Instance.FreyPackage_GaloisRep
public import Def.FreyPackage_LevelRaising
public import Theorem.ValuationSubring.GlobalUnramifiedAt
@[expose] public section

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine.Point

open scoped CongruenceSubgroup

namespace FreyPackage

noncomputable local instance instDecEqQbarExchangeCase :
    DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _

instance (P : FreyPackage) (q : ℕ) : Decidable (P.ExchangeCongruence q) :=
  Int.decidableDvd _ _

end FreyPackage
