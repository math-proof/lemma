module
public import Mathlib
public import Instance.CuspForm_AuxLevelHeckeModule
public import Inductive.CuspForm_TWLevelHeckeModule_Gen
set_option autoImplicit false


public section

noncomputable section

namespace CuspForm.TWLevel

section Level

variable (N r : ℕ) {t : ℕ} (qv : Fin t → ℕ)

abbrev Delta (p : ℕ) : Type := Π i : Fin t, Multiplicative (ZMod (p ^ padicValNat p (qv i - 1)))

end Level

section Ops


end Ops

end CuspForm.TWLevel

end
