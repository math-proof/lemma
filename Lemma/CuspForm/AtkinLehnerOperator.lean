import Mathlib
import Lemma.ModularForm.AtkinLehnerDatum
import Theorems.Thm_ModularForm_alSlash_slash_eq_self_of_mem_Gamma0
import Theorems.Thm_ModularForm_mdifferentiable_alSlash
import Theorems.Thm_ModularForm_isBoundedAt_alSlash
import Theorems.Thm_ModularForm_isZeroAt_alSlash
import Def.CuspForm_AtkinLehnerOperator

set_option autoImplicit false

noncomputable section

namespace ModularForm

variable {M q : ℕ}


@[simp] theorem coe_atkinLehnerLin_apply [NeZero M] (W : AtkinLehnerDatum M q) (k : ℤ)
    (f : ModularForm (CongruenceSubgroup.Gamma0 M) k) : ⇑(atkinLehnerLin W k f) = alSlash W k ⇑f := rfl

end ModularForm

namespace CuspForm

open ModularForm

variable {M q : ℕ}


@[simp] theorem coe_atkinLehnerLin_apply [NeZero M] (W : AtkinLehnerDatum M q) (k : ℤ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 M) k) : ⇑(atkinLehnerLin W k f) = alSlash W k ⇑f := rfl

theorem atkinLehnerLin_apply_apply [NeZero M] (W : AtkinLehnerDatum M q) (k : ℤ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 M) k) (τ : UpperHalfPlane) :
    atkinLehnerLin W k f τ = alSlash W k ⇑f τ := rfl

end CuspForm

end
