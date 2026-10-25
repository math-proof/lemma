import Mathlib
import Lemma.ModularForm.HeckeOperatorForms
import Theorems.Thm_ModularForm_heckeU_slash_eq_self_of_mem_Gamma0_div
import Def.CuspForm_HeckeULower

set_option autoImplicit false

noncomputable section

namespace CuspForm

open ModularForm

variable {N : ℕ} {p : ℕ}


@[simp] theorem coe_heckeULowerLin_apply (k : ℤ) [NeZero N] (hp2N : p ^ 2 ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    ⇑(heckeULowerLin k hp2N f) = heckeU k p ⇑f := rfl

theorem heckeULowerLin_apply_apply (k : ℤ) [NeZero N] (hp2N : p ^ 2 ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (τ : UpperHalfPlane) :
    heckeULowerLin k hp2N f τ = heckeU k p ⇑f τ := rfl

end CuspForm

end
