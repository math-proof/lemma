-- Carved from Lemma/Definitions/Def_NumberField_NormResidueCharacter.lean: instance decls only.
import Mathlib
import Lemma.LanglandsTunnell.NormClass
import Lemma.NumberField.RayCharacterData
import Lemma.NumberField.NormResidueCharacter

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace NumberField.NormResidueChar

open NumberField NumberField.InfinitePlace IsDedekindDomain Deep.NTSupply
open LanglandsTunnell.P2.Artin
open scoped nonZeroDivisors Classical

variable (K : Type) [Field K] [NumberField K] (m : ℕ) [NeZero m]

instance finite_G : Finite (NarrowRayClassGroup K (fm K m)) := Deep.NTSupply.finite K (fm_ne_bot K m)

noncomputable instance fintype_G : Fintype (NarrowRayClassGroup K (fm K m)) := Fintype.ofFinite _

variable {K m}


end NumberField.NormResidueChar

end
