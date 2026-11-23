-- Carved from Lemma/Definitions/Def_ExtCitation_CyclotomicUnits.lean: instance decls only.
module

public import Theorem.ClassGroup.GaloisAction
public import Def.Stickelberger_Basic
@[expose] public section

set_option autoImplicit false

namespace ExtCitation.Cyclotomic

open NumberField JacobiSumStickelberger Stickelberger

variable (p : ℕ) [Fact p.Prime]


set_option backward.isDefEq.respectTransparency false in

noncomputable instance instIsCycExt :
    IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
  inferInstance

end ExtCitation.Cyclotomic
