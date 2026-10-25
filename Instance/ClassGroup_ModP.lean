-- Carved from Lemma/Definitions/Def_ClassGroup_ModP.lean: instance decls only.
import Mathlib
import Lemma.ClassGroup.ModP

set_option autoImplicit false

open scoped NumberField nonZeroDivisors

namespace JacobiSumStickelberger

section ModP

variable (p : ℕ) (M : Type*) [AddCommGroup M]

instance instModuleZModModP [NeZero p] : Module (ZMod p) (ModP p M) :=
  QuotientAddGroup.zmodModule (nsmul_mem_nsmulRange p M)

end ModP


end JacobiSumStickelberger
