module

public import Mathlib
public import Structure.FLTPrelim_FreyPackage
public import Def.FreyPackage_LevelRaising
public import Instance.FreyPackage_GaloisRep
public import Def.GaloisRep_GlobalUnramifiedAt
public import Theorem.MvPolynomial.HeckeModule
public import Def.ModularCurve_HeckeInputsAll
public import Structure.ModularCurve_MazurPrincipleCore
public import Structure.FreyPackage_MazurAttachmentApparatus

set_option autoImplicit false

@[expose] public noncomputable section

namespace FreyPackage

open ModularCurve
open scoped CongruenceSubgroup

abbrev mazurGaloisGroup : Type := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ


end FreyPackage

end
