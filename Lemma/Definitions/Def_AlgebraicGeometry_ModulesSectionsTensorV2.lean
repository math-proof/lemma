import Mathlib
import Lemma.Definitions.Def_PresheafOfModules_InternalHom
import Lemma.Definitions.Def_SheafOfModules_MonoidalV2
import Lemma.Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Lemma.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory MonoidalCategory Opposite TensorProduct

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

section Hom


end Hom

section Sections


end Sections

section Pow


end Pow

section Frame

variable {M : X.Modules} {U : X.Opens}

namespace IsFrameOn


end IsFrameOn

end Frame

end AlgebraicGeometry.Scheme.Modules

end
