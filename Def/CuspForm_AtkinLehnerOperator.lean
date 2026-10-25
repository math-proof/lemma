import Mathlib
import Lemma.ModularForm.AtkinLehnerDatum
import Theorems.Thm_ModularForm_alSlash_slash_eq_self_of_mem_Gamma0
import Theorems.Thm_ModularForm_mdifferentiable_alSlash
import Theorems.Thm_ModularForm_isBoundedAt_alSlash
import Theorems.Thm_ModularForm_isZeroAt_alSlash

set_option autoImplicit false

noncomputable section

namespace ModularForm

variable {M q : ℕ}

def atkinLehnerLin [NeZero M] (W : AtkinLehnerDatum M q) (k : ℤ) :
    ModularForm (CongruenceSubgroup.Gamma0 M) k →ₗ[ℂ] ModularForm (CongruenceSubgroup.Gamma0 M) k where
  toFun f :=
    { toFun := alSlash W k ⇑f
      slash_action_eq' := fun γ hγ => alSlash_slash_eq_self_of_mem_Gamma0 W k
        (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ) γ hγ
      holo' := mdifferentiable_alSlash W k (ModularFormClass.holo f)
      bdd_at_cusps' := fun hc => isBoundedAt_alSlash W k
        (fun c' hc' => ModularFormClass.bdd_at_cusps f hc') hc }
  map_add' f g := DFunLike.coe_injective <|
    show alSlash W k ⇑(f + g) = alSlash W k ⇑f + alSlash W k ⇑g by rw [ModularForm.coe_add, alSlash_add]
  map_smul' c f := DFunLike.coe_injective <|
    show alSlash W k ⇑(c • f) = c • alSlash W k ⇑f by rw [ModularForm.IsGLPos.coe_smul, alSlash_smul]

end ModularForm

namespace CuspForm

open ModularForm

variable {M q : ℕ}

def atkinLehnerLin [NeZero M] (W : AtkinLehnerDatum M q) (k : ℤ) :
    CuspForm (CongruenceSubgroup.Gamma0 M) k →ₗ[ℂ] CuspForm (CongruenceSubgroup.Gamma0 M) k where
  toFun f :=
    { toFun := alSlash W k ⇑f
      slash_action_eq' := fun γ hγ => alSlash_slash_eq_self_of_mem_Gamma0 W k
        (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ) γ hγ
      holo' := mdifferentiable_alSlash W k (CuspFormClass.holo f)
      zero_at_cusps' := fun hc => isZeroAt_alSlash W k
        (fun c' hc' => CuspFormClass.zero_at_cusps f hc') hc }
  map_add' f g := DFunLike.coe_injective <|
    show alSlash W k ⇑(f + g) = alSlash W k ⇑f + alSlash W k ⇑g by rw [CuspForm.coe_add, alSlash_add]
  map_smul' c f := DFunLike.coe_injective <|
    show alSlash W k ⇑(c • f) = c • alSlash W k ⇑f by rw [CuspForm.IsGLPos.coe_smul, alSlash_smul]

end CuspForm

end
