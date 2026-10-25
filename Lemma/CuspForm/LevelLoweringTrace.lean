import Mathlib
import Lemma.ModularForm.HeckeOperator
import Lemma.ModularForm.AtkinLehnerDatum
import Theorems.Thm_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0
import Theorems.Thm_ModularForm_mdifferentiable_add_heckeU_alSlash
import Theorems.Thm_ModularForm_isZeroAt_add_heckeU_alSlash
import Def.CuspForm_LevelLoweringTrace

set_option autoImplicit false

noncomputable section

namespace CuspForm

open ModularForm

variable {M q : ℕ}


@[simp] theorem coe_traceLin_apply [NeZero M] (W : AtkinLehnerDatum M q) (hq : q.Prime)
    (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2) :
    ⇑(traceLin W hq f) = ⇑f + heckeU 2 q (alSlash W 2 ⇑f) := rfl

theorem traceLin_apply_apply [NeZero M] (W : AtkinLehnerDatum M q) (hq : q.Prime)
    (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (τ : UpperHalfPlane) :
    traceLin W hq f τ = f τ + heckeU 2 q (alSlash W 2 ⇑f) τ := rfl

end CuspForm

end
