import Mathlib
import Def.ModularForm_HeckeOperatorForms
import Theorems.Thm_ModularForm_heckeU_slash_eq_self_of_mem_Gamma0_div

set_option autoImplicit false

noncomputable section

namespace CuspForm

open ModularForm

variable {N : ℕ} {p : ℕ}

def heckeULowerLin (k : ℤ) [NeZero N] (hp2N : p ^ 2 ∣ N) :
    CuspForm (CongruenceSubgroup.Gamma0 N) k →ₗ[ℂ] CuspForm (CongruenceSubgroup.Gamma0 (N / p)) k :=
  haveI : NeZero (N / p) := ⟨fun h => by
    have hp : p ≠ 0 := by
      rintro rfl
      exact NeZero.ne N (zero_dvd_iff.mp ((dvd_pow_self 0 two_ne_zero).trans hp2N))
    have hpN : p ∣ N := (dvd_pow_self p two_ne_zero).trans hp2N
    exact Nat.div_ne_zero_iff.mpr ⟨hp, Nat.le_of_dvd (NeZero.pos N) hpN⟩ h⟩
  { toFun := fun f =>
    { toFun := heckeU k p ⇑f
      slash_action_eq' := fun γ hγ => heckeU_slash_eq_self_of_mem_Gamma0_div k hp2N
        (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ) γ hγ
      holo' := mdifferentiable_heckeU (CuspFormClass.holo f) k p
      zero_at_cusps' := fun {c} hc => CuspFormClass.isZeroAt_heckeU f p
        ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mpr
          ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mp hc)) }
    map_add' := fun f g => DFunLike.coe_injective <|
      show heckeU k p ⇑(f + g) = heckeU k p ⇑f + heckeU k p ⇑g by rw [CuspForm.coe_add, heckeU_add]
    map_smul' := fun c f => DFunLike.coe_injective <|
      show heckeU k p ⇑(c • f) = c • heckeU k p ⇑f by rw [CuspForm.IsGLPos.coe_smul, heckeU_smul] }

end CuspForm

end
