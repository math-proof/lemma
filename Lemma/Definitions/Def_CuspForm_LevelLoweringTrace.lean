import Mathlib
import Lemma.Definitions.Def_ModularForm_HeckeOperator
import Lemma.Definitions.Def_ModularForm_AtkinLehnerDatum
import Theorems.Thm_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0
import Theorems.Thm_ModularForm_mdifferentiable_add_heckeU_alSlash
import Theorems.Thm_ModularForm_isZeroAt_add_heckeU_alSlash

set_option autoImplicit false

noncomputable section

namespace CuspForm

open ModularForm

variable {M q : ℕ}

def traceLin [NeZero M] (W : AtkinLehnerDatum M q) (hq : q.Prime) :
    CuspForm (CongruenceSubgroup.Gamma0 M) 2 →ₗ[ℂ] CuspForm (CongruenceSubgroup.Gamma0 W.R) 2 where
  toFun f :=
    { toFun := ⇑f + heckeU 2 q (alSlash W 2 ⇑f)
      slash_action_eq' := fun γ hγ => add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0 W hq
        (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ) γ hγ
      holo' := mdifferentiable_add_heckeU_alSlash W 2 (CuspFormClass.holo f)
      zero_at_cusps' := fun hc => isZeroAt_add_heckeU_alSlash W 2
        (fun c' hc' => CuspFormClass.zero_at_cusps f hc') hc }
  map_add' f g := DFunLike.coe_injective <|
    show ⇑(f + g) + heckeU 2 q (alSlash W 2 ⇑(f + g))
        = (⇑f + heckeU 2 q (alSlash W 2 ⇑f)) + (⇑g + heckeU 2 q (alSlash W 2 ⇑g)) by
      rw [CuspForm.coe_add, alSlash_add, heckeU_add]; abel
  map_smul' c f := DFunLike.coe_injective <|
    show ⇑(c • f) + heckeU 2 q (alSlash W 2 ⇑(c • f)) = c • (⇑f + heckeU 2 q (alSlash W 2 ⇑f)) by
      rw [CuspForm.IsGLPos.coe_smul, alSlash_smul, heckeU_smul, smul_add]

@[simp] theorem coe_traceLin_apply [NeZero M] (W : AtkinLehnerDatum M q) (hq : q.Prime)
    (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2) :
    ⇑(traceLin W hq f) = ⇑f + heckeU 2 q (alSlash W 2 ⇑f) := rfl

theorem traceLin_apply_apply [NeZero M] (W : AtkinLehnerDatum M q) (hq : q.Prime)
    (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (τ : UpperHalfPlane) :
    traceLin W hq f τ = f τ + heckeU 2 q (alSlash W 2 ⇑f) τ := rfl

end CuspForm

end
