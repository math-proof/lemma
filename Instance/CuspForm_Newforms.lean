-- Carved from Lemma/Definitions/Def_CuspForm_Newforms.lean: instance decls only.
module

public import Def.FreyPackage_LevelRaising
public import Instance.FLTPrelim_GaloisRep
@[expose] public section

set_option autoImplicit false

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine.Point
open ModularFormClass


namespace FreyPackage

open CuspForm

noncomputable local instance instDecEqQbarNewforms :
    DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _

end FreyPackage

end
