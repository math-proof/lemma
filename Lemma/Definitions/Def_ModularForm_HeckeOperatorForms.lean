import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Lemma.Definitions.Def_ModularForm_HeckeOperator
import Theorems.Thm_ModularForm_heckeT_slash_eq_self_of_mem_Gamma0
import Theorems.Thm_ModularForm_heckeU_slash_eq_self_of_mem_Gamma0
import Theorems.Thm_ModularForm_mdifferentiable_heckeT
import Theorems.Thm_ModularForm_mdifferentiable_heckeU
import Theorems.Thm_ModularFormClass_isBoundedAt_heckeT
import Theorems.Thm_ModularFormClass_isBoundedAt_heckeU
import Theorems.Thm_CuspFormClass_isZeroAt_heckeT
import Theorems.Thm_CuspFormClass_isZeroAt_heckeU

set_option autoImplicit false

noncomputable section

namespace ModularForm

variable {N : ℕ} {p : ℕ}

def heckeTLin (k : ℤ) (hp : p.Prime) (hpN : ¬ p ∣ N) :
    ModularForm (CongruenceSubgroup.Gamma0 N) k →ₗ[ℂ] ModularForm (CongruenceSubgroup.Gamma0 N) k :=
  haveI : NeZero N := ⟨fun h => hpN (h ▸ dvd_zero p)⟩
  { toFun := fun f =>
      { toFun := heckeT k p ⇑f
        slash_action_eq' := fun γ hγ => heckeT_slash_eq_self_of_mem_Gamma0 k hp hpN
          (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ) γ hγ
        holo' := mdifferentiable_heckeT (ModularFormClass.holo f) k p
        bdd_at_cusps' := fun hc => ModularFormClass.isBoundedAt_heckeT f p hc }
    map_add' := fun f g => DFunLike.coe_injective <|
      show heckeT k p ⇑(f + g) = heckeT k p ⇑f + heckeT k p ⇑g by rw [ModularForm.coe_add, heckeT_add]
    map_smul' := fun c f => DFunLike.coe_injective <|
      show heckeT k p ⇑(c • f) = c • heckeT k p ⇑f by rw [ModularForm.IsGLPos.coe_smul, heckeT_smul] }

def heckeULin (k : ℤ) [NeZero N] (hpN : p ∣ N) :
    ModularForm (CongruenceSubgroup.Gamma0 N) k →ₗ[ℂ] ModularForm (CongruenceSubgroup.Gamma0 N) k where
  toFun f :=
    { toFun := heckeU k p ⇑f
      slash_action_eq' := fun γ hγ => heckeU_slash_eq_self_of_mem_Gamma0 k hpN
        (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ) γ hγ
      holo' := mdifferentiable_heckeU (ModularFormClass.holo f) k p
      bdd_at_cusps' := fun hc => ModularFormClass.isBoundedAt_heckeU f p hc }
  map_add' f g := DFunLike.coe_injective <|
    show heckeU k p ⇑(f + g) = heckeU k p ⇑f + heckeU k p ⇑g by rw [ModularForm.coe_add, heckeU_add]
  map_smul' c f := DFunLike.coe_injective <|
    show heckeU k p ⇑(c • f) = c • heckeU k p ⇑f by rw [ModularForm.IsGLPos.coe_smul, heckeU_smul]

@[simp] theorem coe_heckeTLin_apply (k : ℤ) (hp : p.Prime) (hpN : ¬ p ∣ N)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) : ⇑(heckeTLin k hp hpN f) = heckeT k p ⇑f := rfl

@[simp] theorem coe_heckeULin_apply (k : ℤ) [NeZero N] (hpN : p ∣ N)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) : ⇑(heckeULin k hpN f) = heckeU k p ⇑f := rfl

theorem heckeTLin_apply_apply (k : ℤ) (hp : p.Prime) (hpN : ¬ p ∣ N)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) (τ : UpperHalfPlane) :
    heckeTLin k hp hpN f τ = heckeT k p ⇑f τ := rfl

theorem heckeULin_apply_apply (k : ℤ) [NeZero N] (hpN : p ∣ N)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) (τ : UpperHalfPlane) :
    heckeULin k hpN f τ = heckeU k p ⇑f τ := rfl

end ModularForm

namespace CuspForm

open ModularForm

variable {N : ℕ} {p : ℕ}

def heckeTLin (k : ℤ) (hp : p.Prime) (hpN : ¬ p ∣ N) :
    CuspForm (CongruenceSubgroup.Gamma0 N) k →ₗ[ℂ] CuspForm (CongruenceSubgroup.Gamma0 N) k :=
  haveI : NeZero N := ⟨fun h => hpN (h ▸ dvd_zero p)⟩
  { toFun := fun f =>
      { toFun := heckeT k p ⇑f
        slash_action_eq' := fun γ hγ => heckeT_slash_eq_self_of_mem_Gamma0 k hp hpN
          (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ) γ hγ
        holo' := mdifferentiable_heckeT (CuspFormClass.holo f) k p
        zero_at_cusps' := fun hc => CuspFormClass.isZeroAt_heckeT f p hc }
    map_add' := fun f g => DFunLike.coe_injective <|
      show heckeT k p ⇑(f + g) = heckeT k p ⇑f + heckeT k p ⇑g by rw [CuspForm.coe_add, heckeT_add]
    map_smul' := fun c f => DFunLike.coe_injective <|
      show heckeT k p ⇑(c • f) = c • heckeT k p ⇑f by rw [CuspForm.IsGLPos.coe_smul, heckeT_smul] }

def heckeULin (k : ℤ) [NeZero N] (hpN : p ∣ N) :
    CuspForm (CongruenceSubgroup.Gamma0 N) k →ₗ[ℂ] CuspForm (CongruenceSubgroup.Gamma0 N) k where
  toFun f :=
    { toFun := heckeU k p ⇑f
      slash_action_eq' := fun γ hγ => heckeU_slash_eq_self_of_mem_Gamma0 k hpN
        (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ) γ hγ
      holo' := mdifferentiable_heckeU (CuspFormClass.holo f) k p
      zero_at_cusps' := fun hc => CuspFormClass.isZeroAt_heckeU f p hc }
  map_add' f g := DFunLike.coe_injective <|
    show heckeU k p ⇑(f + g) = heckeU k p ⇑f + heckeU k p ⇑g by rw [CuspForm.coe_add, heckeU_add]
  map_smul' c f := DFunLike.coe_injective <|
    show heckeU k p ⇑(c • f) = c • heckeU k p ⇑f by rw [CuspForm.IsGLPos.coe_smul, heckeU_smul]

@[simp] theorem coe_heckeTLin_apply (k : ℤ) (hp : p.Prime) (hpN : ¬ p ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) : ⇑(heckeTLin k hp hpN f) = heckeT k p ⇑f := rfl

@[simp] theorem coe_heckeULin_apply (k : ℤ) [NeZero N] (hpN : p ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) : ⇑(heckeULin k hpN f) = heckeU k p ⇑f := rfl

theorem heckeTLin_apply_apply (k : ℤ) (hp : p.Prime) (hpN : ¬ p ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (τ : UpperHalfPlane) :
    heckeTLin k hp hpN f τ = heckeT k p ⇑f τ := rfl

theorem heckeULin_apply_apply (k : ℤ) [NeZero N] (hpN : p ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (τ : UpperHalfPlane) :
    heckeULin k hpN f τ = heckeU k p ⇑f τ := rfl

end CuspForm

end
