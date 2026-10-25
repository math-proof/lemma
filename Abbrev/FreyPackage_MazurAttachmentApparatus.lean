import Mathlib
import Structure.FLTPrelim_FreyPackage
import Def.FreyPackage_LevelRaising
import Instance.FreyPackage_GaloisRep
import Def.GaloisRep_GlobalUnramifiedAt
import Lemma.ModularCurve.HeckeModule
import Def.ModularCurve_HeckeInputsAll
import Structure.ModularCurve_MazurPrincipleCore
import Structure.FreyPackage_MazurAttachmentApparatus

set_option autoImplicit false

noncomputable section

namespace FreyPackage

open ModularCurve
open scoped CongruenceSubgroup

abbrev mazurGaloisGroup : Type := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ


end FreyPackage

end
