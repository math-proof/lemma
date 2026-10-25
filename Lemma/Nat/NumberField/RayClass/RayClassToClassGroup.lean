import Mathlib
import sympy.Basic
import Theorem.NumberTheory.NumberField.RayClass.RayClassToClassGroup.Part2
open scoped nonZeroDivisors
open NumberField
open Modulus


namespace NumberField.Modulus

/--
[rayClassToClassGroup_comp_rayClassMap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/RayClassToClassGroup.lean)
-/
@[path]
lemma rayClassToClassGroup_comp_rayClassMap
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  (rayClassToClassGroup m).comp (rayClassMap m) = coprimeIdealClassMap m := by
-- proof
  ext I
  simp only [MonoidHom.comp_apply]
  exact rayClassToClassGroup_rayClassMap m I

end NumberField.Modulus

namespace NumberField.Modulus

/--
[rayClassToClassGroup_rayQuotientToRayClassGroup](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/RayClassToClassGroup.lean)
-/
@[path]
lemma rayClassToClassGroup_rayQuotientToRayClassGroup
  [Field K] [NumberField K]
  {m : Modulus K}
  {x : rayElements m} :
-- imply
  rayClassToClassGroup m (rayQuotientToRayClassGroup m (QuotientGroup.mk x)) =
    coprimeIdealClassMap m (principalRayIdealMap m x) := by
-- proof
  rw [rayQuotientToRayClassGroup_mk, rayElementClassMap_apply,
    ← rayClassToClassGroup_rayClassMap]

end NumberField.Modulus

namespace NumberField.Modulus

/--
[rayClassToClassGroup_residueSignToRayClassGroup](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/RayClassToClassGroup.lean)
-/
@[path]
lemma rayClassToClassGroup_residueSignToRayClassGroup
  [Field K] [NumberField K]
  {m : Modulus K}
  {x : rayElements m} :
-- imply
  rayClassToClassGroup m
    (residueSignToRayClassGroup m (residueSignMap m x)) =
    coprimeIdealClassMap m (principalRayIdealMap m x) := by
-- proof
  rw [residueSignToRayClassGroup_residueSignMap,
    rayElementClassMap_apply, ← rayClassToClassGroup_rayClassMap]

end NumberField.Modulus

namespace NumberField.Modulus

/--
[rayClassToClassGroup_ker](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/RayClassToClassGroup.lean)
-/
@[path]
lemma rayClassToClassGroup_ker
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  (rayClassToClassGroup m).ker =
    MonoidHom.range (rayQuotientToRayClassGroup m) := by
-- proof
  apply le_antisymm
  · intro c hc
    rw [MonoidHom.mem_ker] at hc
    obtain ⟨I, rfl⟩ := rayClassMap_surjective m c
    rw [rayClassToClassGroup_rayClassMap] at hc
    have hunfold : ClassGroup.mk K
      ((coprimeFractionalIdeals m).subtype I) = 1 := hc
    rw [ClassGroup.mk_eq_one_iff, FractionalIdeal.isPrincipal_iff] at hunfold
    obtain ⟨a, ha⟩ := hunfold
    have ha_val : ((((coprimeFractionalIdeals m).subtype I :
      (FractionalIdeal (𝓞 K)⁰ K)ˣ)) : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ a := ha
    have ha_val' : ((I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ a := by
      simpa only [Subgroup.coe_subtype] using ha_val
    have ha_ne : a ≠ 0 := by
      intro ha_zero
      rw [ha_zero, FractionalIdeal.spanSingleton_zero] at ha_val'
      exact Units.ne_zero (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) ha_val'
    set α : Kˣ := Units.mk0 a ha_ne with hα
    have hI_eq_topi : (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) =
      toPrincipalIdeal (𝓞 K) K α := by
      apply Units.ext
      show ((I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) = _
      rwa [coe_toPrincipalIdeal, hα, Units.val_mk0]
    have hα_coprime : α ∈ rayElements m := by
      rwa [mem_rayElements_iff, ← hI_eq_topi]
    set γ : rayElements m := ⟨α, hα_coprime⟩ with hγ
    have hγ_eq : principalRayIdealMap m γ = I := by
      apply Subtype.ext
      have h := principalRayIdealMap_apply m γ
      rw [h, hI_eq_topi]
    refine MonoidHom.mem_range.mpr ⟨QuotientGroup.mk γ, ?_⟩
    rw [rayQuotientToRayClassGroup_mk, rayElementClassMap_apply, hγ_eq]
  · intro c hc
    obtain ⟨q, rfl⟩ := MonoidHom.mem_range.mp hc
    rw [MonoidHom.mem_ker]
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (rayOneElements m) q
    rw [QuotientGroup.mk'_apply, rayQuotientToRayClassGroup_mk,
      rayElementClassMap_apply, rayClassToClassGroup_rayClassMap]
    rw [coprimeIdealClassMap_apply, ClassGroup.mk_eq_one_iff,
      FractionalIdeal.isPrincipal_iff]
    refine ⟨((x : Kˣ) : K), ?_⟩
    have h := principalRayIdealMap_apply m x
    have hval : (((principalRayIdealMap m x :
      coprimeFractionalIdeals m) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ ((x : Kˣ) : K) := by
      rw [h, coe_toPrincipalIdeal]
    simpa only [Subgroup.coe_subtype] using hval

end NumberField.Modulus

namespace NumberField.Modulus

/--
[rayQuotientToRayClassGroup_mulExact_rayClassToClassGroup](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/RayClassToClassGroup.lean)
-/
@[path]
lemma rayQuotientToRayClassGroup_mulExact_rayClassToClassGroup
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  Function.MulExact (rayQuotientToRayClassGroup m)
    (rayClassToClassGroup m) := by
-- proof
  rw [MonoidHom.mulExact_iff, rayClassToClassGroup_ker]

end NumberField.Modulus

namespace NumberField.Modulus

/--
[residueSignToRayClassGroup_mulExact_rayClassToClassGroup](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/RayClassToClassGroup.lean)
-/
@[path]
lemma residueSignToRayClassGroup_mulExact_rayClassToClassGroup
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  Function.MulExact (residueSignToRayClassGroup m)
    (rayClassToClassGroup m) := by
-- proof
  rw [MonoidHom.mulExact_iff]
  have hrange : MonoidHom.range (residueSignToRayClassGroup m) =
    MonoidHom.range (rayQuotientToRayClassGroup m) := by
    unfold residueSignToRayClassGroup
    rw [MonoidHom.range_comp, MulEquiv.toMonoidHom_eq_coe,
      MulEquiv.range_eq_top, ← MonoidHom.range_eq_map]
  rw [hrange, ← rayClassToClassGroup_ker]

end NumberField.Modulus

/--
[coprimeIdealClassMap_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/RayClassToClassGroup.lean)
-/
@[path]
private lemma coprimeIdealClassMap_apply_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {I : coprimeFractionalIdeals m} :
-- imply
  coprimeIdealClassMap m I =
    ClassGroup.mk K ((coprimeFractionalIdeals m).subtype I) := by
-- proof
  apply NumberField.Modulus.coprimeIdealClassMap_apply m I

/--
[rayGroup_le_coprimeIdealClassMap_ker](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/RayClassToClassGroup.lean)
-/
@[path]
private lemma rayGroup_le_coprimeIdealClassMap_ker_eq
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  rayGroup m ≤ (coprimeIdealClassMap m).ker := by
-- proof
  apply NumberField.Modulus.rayGroup_le_coprimeIdealClassMap_ker m

/--
[rayClassToClassGroup_rayClassMap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/RayClassToClassGroup.lean)
-/
@[path]
private lemma rayClassToClassGroup_rayClassMap_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {I : coprimeFractionalIdeals m} :
-- imply
  rayClassToClassGroup m (rayClassMap m I) = coprimeIdealClassMap m I := by
-- proof
  apply NumberField.Modulus.rayClassToClassGroup_rayClassMap m I


-- created on 2026-10-20
-- updated on 2026-10-23
