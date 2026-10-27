import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.NumberTheoryI.code.Prop226
open RayClassField
open scoped NumberField


namespace RayClassField

/--
[Modulus.gcd_dvd_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop226.lean)
-/
@[path]
lemma Modulus.gcd_dvd_left
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪₁ 𝔪₂ : Modulus K} :
-- imply
  (𝔪₁.gcd 𝔪₂).dvd 𝔪₁ :=
-- proof
  fun _ => min_le_left _ _

end RayClassField

namespace RayClassField

/--
[Modulus.gcd_dvd_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop226.lean)
-/
@[path]
lemma Modulus.gcd_dvd_right
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪₁ 𝔪₂ : Modulus K} :
-- imply
  (𝔪₁.gcd 𝔪₂).dvd 𝔪₂ :=
-- proof
  fun _ => min_le_right _ _

end RayClassField

namespace RayClassField

/--
[theorem_8_5_ray_gen_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop226.lean)
-/
@[path]
lemma theorem_8_5_ray_gen_decomp
  {K : Type u}
  [Field K]
  [NumberField K]
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪₁ 𝔪₂ : Modulus K}
  {I : FracIdealsCoprime K (𝔪₁.gcd 𝔪₂)}
-- given
  (hI : IsRayGenerator (𝔪₁.gcd 𝔪₂) I) :
-- imply
  ∃ (I₁ : FracIdealsCoprime K 𝔪₁) (I₂ : FracIdealsCoprime K 𝔪₂), IsRayGenerator 𝔪₁ I₁ ∧ IsRayGenerator 𝔪₂ I₂ ∧ (FracIdealsCoprime_subgroup K (𝔪₁.gcd 𝔪₂)).subtype I = (FracIdealsCoprime_subgroup K 𝔪₁).subtype I₁ * (FracIdealsCoprime_subgroup K 𝔪₂).subtype I₂ := by
-- proof
  classical
  obtain ⟨α, hα_eq, hα_val, hα_sign⟩ := hI
  have hα_cop : ∀ v : FinitePlace K, (𝔪₁.gcd 𝔪₂) (Place.finite v) ≠ 0 →
    v.valuation K (α : K) = 1 := by
    intro v hv
    have hI_cop := I.property v hv
    have hI_val_eq : I.val = toPrincipalIdeal (𝓞 K) K α := by
      apply Units.val_injective
      rwa [coe_toPrincipalIdeal]
    rw [hI_val_eq] at hI_cop
    obtain ⟨x, hx_mem, hx_val⟩ := hI_cop.1
    simp only [coe_toPrincipalIdeal] at hx_mem
    have h_inv : HasTrivialValuation ((toPrincipalIdeal (𝓞 K) K α)⁻¹) v := hI_cop.2
    rw [← MonoidHom.map_inv] at h_inv
    obtain ⟨y, hy_mem, hy_val⟩ := h_inv
    simp only [coe_toPrincipalIdeal] at hy_mem
    rw [FractionalIdeal.mem_spanSingleton] at hx_mem hy_mem
    obtain ⟨r, hr⟩ := hx_mem
    obtain ⟨s, hs⟩ := hy_mem
    subst hr; subst hs
    simp only [Algebra.smul_def] at hx_val hy_val
    rw [map_mul] at hx_val hy_val
    have hr_le : v.valuation K (algebraMap _ K r) ≤ 1 := v.valuation_le_one r
    have hs_le : v.valuation K (algebraMap _ K s) ≤ 1 := v.valuation_le_one s
    have hαα : v.valuation K (α : K) * v.valuation K ((α⁻¹ : Kˣ) : K) = 1 := by
      rw [← map_mul, show (α : K) * ((α⁻¹ : Kˣ) : K) = 1 from by simp, map_one]
    apply le_antisymm
    · calc v.valuation K (α : K)
      = v.valuation K (α : K) * 1 := (mul_one _).symm
      _ = v.valuation K (α : K) * (v.valuation K (algebraMap _ K s) *
        v.valuation K ((α⁻¹ : Kˣ) : K)) := by rw [hy_val]
      _ = (v.valuation K (α : K) * v.valuation K ((α⁻¹ : Kˣ) : K)) *
        v.valuation K (algebraMap _ K s) := by
          rw [mul_assoc, mul_comm (v.valuation K (algebraMap _ K s))]
      _ = 1 * v.valuation K (algebraMap _ K s) := by rw [hαα]
      _ = v.valuation K (algebraMap _ K s) := one_mul _
      _ ≤ 1 := hs_le
    · calc (1 : WithZero (Multiplicative ℤ))
      = v.valuation K (algebraMap _ K r) * v.valuation K (α : K) := hx_val.symm
      _ ≤ 1 * v.valuation K (α : K) := by gcongr
      _ = v.valuation K (α : K) := one_mul _
  obtain ⟨β, hαβ_cop, hαβ_val, hαβ_sign, hβinv_cop, hβinv_val, hβinv_sign⟩ :=
    weak_approx_ray_gen_aux' 𝔪₁ 𝔪₂ α hα_cop hα_val hα_sign
  have hαβ_in_coprime : (α * β) ∈ UnitsCoprime_subgroup' K 𝔪₁ := hαβ_cop
  have hβinv_in_coprime : β⁻¹ ∈ UnitsCoprime_subgroup' K 𝔪₂ := hβinv_cop
  let I₁ : FracIdealsCoprime K 𝔪₁ :=
    ⟨toPrincipalIdeal (𝓞 K) K (α * β),
      toPrincipalIdeal_mem_FracIdealsCoprime 𝔪₁ (α * β) hαβ_in_coprime⟩
  let I₂ : FracIdealsCoprime K 𝔪₂ :=
    ⟨toPrincipalIdeal (𝓞 K) K β⁻¹,
      toPrincipalIdeal_mem_FracIdealsCoprime 𝔪₂ β⁻¹ hβinv_in_coprime⟩
  refine ⟨I₁, I₂, ?_, ?_, ?_⟩
  ·
    exact ⟨α * β, coe_toPrincipalIdeal (α * β), hαβ_val, hαβ_sign⟩
  ·
    exact ⟨β⁻¹, coe_toPrincipalIdeal β⁻¹, hβinv_val, hβinv_sign⟩
  ·
    apply Units.ext
    simp only [Subgroup.coe_subtype, Units.val_mul]
    have hI_val_eq : I.val = toPrincipalIdeal (𝓞 K) K α := by
      apply Units.val_injective
      rwa [coe_toPrincipalIdeal]
    simp only [hI_val_eq]
    have hI1_coe : (I₁.val.val : FracIdeal K) = (toPrincipalIdeal (𝓞 K) K (α * β)).val := rfl
    have hI2_coe : (I₂.val.val : FracIdeal K) = (toPrincipalIdeal (𝓞 K) K β⁻¹).val := rfl
    rw [hI1_coe, hI2_coe]
    simp only [coe_toPrincipalIdeal]
    rw [show ((α * β : Kˣ) : K) = (α : K) * (β : K) from Units.val_mul α β,
      show ((β⁻¹ : Kˣ) : K) = (β : K)⁻¹ from Units.val_inv_eq_inv_val β,
      FractionalIdeal.spanSingleton_mul_spanSingleton]
    congr 1
    field_simp

end RayClassField

namespace RayClassField

/--
[ray_generator_gcd_decomp_aux](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop226.lean)
-/
@[path]
lemma ray_generator_gcd_decomp_aux
  {K : Type u}
  [Field K]
  [NumberField K]
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪₁ 𝔪₂ : Modulus K}
  {I : FracIdealsCoprime K (𝔪₁.gcd 𝔪₂)}
-- given
  (hI : IsRayGenerator (𝔪₁.gcd 𝔪₂) I) :
-- imply
  ∃ (I₁ : FracIdealsCoprime K 𝔪₁) (I₂ : FracIdealsCoprime K 𝔪₂), IsRayGenerator 𝔪₁ I₁ ∧ IsRayGenerator 𝔪₂ I₂ ∧ (FracIdealsCoprime_subgroup K (𝔪₁.gcd 𝔪₂)).subtype I = (FracIdealsCoprime_subgroup K 𝔪₁).subtype I₁ * (FracIdealsCoprime_subgroup K 𝔪₂).subtype I₂ :=
-- proof
  theorem_8_5_ray_gen_decomp 𝔪₁ 𝔪₂ I hI

end RayClassField

namespace RayClassField

/--
[ray_generator_gcd_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop226.lean)
-/
@[path]
lemma ray_generator_gcd_decomp
  {K : Type u}
  [Field K]
  [NumberField K]
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪₁ 𝔪₂ : Modulus K}
  {I : FracIdealsCoprime K (𝔪₁.gcd 𝔪₂)}
-- given
  (hI : IsRayGenerator (𝔪₁.gcd 𝔪₂) I) :
-- imply
  ∃ (J₁ : (FracIdeal K)ˣ) (J₂ : (FracIdeal K)ˣ), J₁ ∈ RayGroup.toAmbientSubgroup K 𝔪₁ ∧ J₂ ∈ RayGroup.toAmbientSubgroup K 𝔪₂ ∧ (FracIdealsCoprime_subgroup K (𝔪₁.gcd 𝔪₂)).subtype I = J₁ * J₂ := by
-- proof
  obtain ⟨I₁, I₂, hI₁, hI₂, hprod⟩ := ray_generator_gcd_decomp_aux 𝔪₁ 𝔪₂ I hI
  refine ⟨(FracIdealsCoprime_subgroup K 𝔪₁).subtype I₁,
    (FracIdealsCoprime_subgroup K 𝔪₂).subtype I₂, ?_, ?_, hprod⟩
  ·
    rw [RayGroup.toAmbientSubgroup]
    exact Subgroup.mem_map.mpr ⟨I₁, Subgroup.subset_closure hI₁, rfl⟩
  ·
    rw [RayGroup.toAmbientSubgroup]
    exact Subgroup.mem_map.mpr ⟨I₂, Subgroup.subset_closure hI₂, rfl⟩

end RayClassField

namespace RayClassField

/--
[ray_generator_gcd_mem_sup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop226.lean)
-/
@[path]
lemma ray_generator_gcd_mem_sup
  {K : Type u}
  [Field K]
  [NumberField K]
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪₁ 𝔪₂ : Modulus K}
  {I : FracIdealsCoprime K (𝔪₁.gcd 𝔪₂)}
-- given
  (hI : IsRayGenerator (𝔪₁.gcd 𝔪₂) I) :
-- imply
  (FracIdealsCoprime_subgroup K (𝔪₁.gcd 𝔪₂)).subtype I ∈ RayGroup.toAmbientSubgroup K 𝔪₁ ⊔ RayGroup.toAmbientSubgroup K 𝔪₂ := by
-- proof
  obtain ⟨J₁, J₂, hJ₁, hJ₂, hprod⟩ := ray_generator_gcd_decomp 𝔪₁ 𝔪₂ I hI
  rw [hprod]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hJ₁) (Subgroup.mem_sup_right hJ₂)

end RayClassField

namespace RayClassField

/--
[theorem_8_5_ray_group_gcd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop226.lean)
-/
@[path]
lemma theorem_8_5_ray_group_gcd
  {K : Type u}
  [Field K]
  [NumberField K]
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪₁ 𝔪₂ : Modulus K} :
-- imply
  RayGroup.toAmbientSubgroup K (𝔪₁.gcd 𝔪₂) ≤ RayGroup.toAmbientSubgroup K 𝔪₁ ⊔ RayGroup.toAmbientSubgroup K 𝔪₂ := by
-- proof
  intro x hx
  rw [RayGroup.toAmbientSubgroup, Subgroup.mem_map] at hx
  obtain ⟨y, hy_mem, rfl⟩ := hx
  suffices h : RayGroup K (𝔪₁.gcd 𝔪₂) ≤
    (RayGroup.toAmbientSubgroup K 𝔪₁ ⊔ RayGroup.toAmbientSubgroup K 𝔪₂).comap
      (FracIdealsCoprime_subgroup K (𝔪₁.gcd 𝔪₂)).subtype by
    exact (h hy_mem)
  rw [RayGroup, Subgroup.closure_le]
  intro I hI
  show (FracIdealsCoprime_subgroup K (𝔪₁.gcd 𝔪₂)).subtype I ∈
    RayGroup.toAmbientSubgroup K 𝔪₁ ⊔ RayGroup.toAmbientSubgroup K 𝔪₂
  exact ray_generator_gcd_mem_sup 𝔪₁ 𝔪₂ I hI

end RayClassField

namespace RayClassField

/--
[equiv_gcd_ray_le_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop226.lean)
-/
@[path]
lemma equiv_gcd_ray_le_left
  {K : Type u}
  [Field K]
  [NumberField K]
  {p₁ p₂ : CongruenceSubgroupPair K}
-- given
  (hequiv : p₁.IsEquiv p₂) :
-- imply
  FracIdealsCoprime_subgroup K p₁.modulus ⊓ RayGroup.toAmbientSubgroup K (p₁.modulus.gcd p₂.modulus) ≤ p₁.toAmbientSubgroup := by
-- proof
  set 𝔪₁ := p₁.modulus
  set 𝔪₂ := p₂.modulus
  have hR₁_le_C₁ : RayGroup.toAmbientSubgroup K 𝔪₁ ≤ p₁.toAmbientSubgroup := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_map.mpr ⟨y, p₁.ray_le hy, rfl⟩
  have hR₂_le_C₂ : RayGroup.toAmbientSubgroup K 𝔪₂ ≤ p₂.toAmbientSubgroup := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_map.mpr ⟨y, p₂.ray_le hy, rfl⟩
  have hR₁_le_I₁ : RayGroup.toAmbientSubgroup K 𝔪₁ ≤
    FracIdealsCoprime_subgroup K 𝔪₁ :=
    RayGroup.toAmbientSubgroup_le 𝔪₁
  have hI₁_cap_R₂_le_C₁ : FracIdealsCoprime_subgroup K 𝔪₁ ⊓
    RayGroup.toAmbientSubgroup K 𝔪₂ ≤ p₁.toAmbientSubgroup := by
    intro y ⟨hy_I₁, hy_R₂⟩
    have : y ∈ FracIdealsCoprime_subgroup K 𝔪₁ ⊓ p₂.toAmbientSubgroup :=
      ⟨hy_I₁, hR₂_le_C₂ hy_R₂⟩
    rwa [hequiv] at this
  intro x ⟨hx_I₁, hx_R_n⟩
  have hx_sup := theorem_8_5_ray_group_gcd K 𝔪₁ 𝔪₂ hx_R_n
  have hx_inter : x ∈ FracIdealsCoprime_subgroup K 𝔪₁ ⊓
    (RayGroup.toAmbientSubgroup K 𝔪₁ ⊔ RayGroup.toAmbientSubgroup K 𝔪₂) :=
    ⟨hx_I₁, hx_sup⟩
  rw [inf_comm, sup_inf_assoc_of_le _ hR₁_le_I₁, inf_comm] at hx_inter
  exact sup_le hR₁_le_C₁ hI₁_cap_R₂_le_C₁ hx_inter

end RayClassField

namespace RayClassField

/--
[equiv_gcd_ray_le_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop226.lean)
-/
@[path]
lemma equiv_gcd_ray_le_right
  {K : Type u}
  [Field K]
  [NumberField K]
  {p₁ p₂ : CongruenceSubgroupPair K}
-- given
  (hequiv : p₁.IsEquiv p₂) :
-- imply
  FracIdealsCoprime_subgroup K p₂.modulus ⊓ RayGroup.toAmbientSubgroup K (p₁.modulus.gcd p₂.modulus) ≤ p₂.toAmbientSubgroup := by
-- proof
  set 𝔪₁ := p₁.modulus
  set 𝔪₂ := p₂.modulus
  have hR₁_le_C₁ : RayGroup.toAmbientSubgroup K 𝔪₁ ≤ p₁.toAmbientSubgroup := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_map.mpr ⟨y, p₁.ray_le hy, rfl⟩
  have hR₂_le_C₂ : RayGroup.toAmbientSubgroup K 𝔪₂ ≤ p₂.toAmbientSubgroup := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_map.mpr ⟨y, p₂.ray_le hy, rfl⟩
  have hR₂_le_I₂ : RayGroup.toAmbientSubgroup K 𝔪₂ ≤
    FracIdealsCoprime_subgroup K 𝔪₂ :=
    RayGroup.toAmbientSubgroup_le 𝔪₂
  have hI₂_cap_R₁_le_C₂ : FracIdealsCoprime_subgroup K 𝔪₂ ⊓
    RayGroup.toAmbientSubgroup K 𝔪₁ ≤ p₂.toAmbientSubgroup := by
    intro y ⟨hy_I₂, hy_R₁⟩
    have : y ∈ FracIdealsCoprime_subgroup K 𝔪₂ ⊓ p₁.toAmbientSubgroup :=
      ⟨hy_I₂, hR₁_le_C₁ hy_R₁⟩
    rwa [← hequiv] at this
  intro x ⟨hx_I₂, hx_R_n⟩
  have hx_sup := theorem_8_5_ray_group_gcd K 𝔪₁ 𝔪₂ hx_R_n
  have hx_inter : x ∈ FracIdealsCoprime_subgroup K 𝔪₂ ⊓
    (RayGroup.toAmbientSubgroup K 𝔪₁ ⊔ RayGroup.toAmbientSubgroup K 𝔪₂) :=
    ⟨hx_I₂, hx_sup⟩
  rw [inf_comm, sup_comm, sup_inf_assoc_of_le _ hR₂_le_I₂, inf_comm] at hx_inter
  exact sup_le hR₂_le_C₂ hI₂_cap_R₁_le_C₂ hx_inter

end RayClassField

/--
[Modulus.dvd_lcm_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop226.lean)
-/
@[path]
private lemma dvd_lcm_left_eq
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪₁ 𝔪₂ : Modulus K} :
-- imply
  𝔪₁.dvd (𝔪₁.lcm 𝔪₂) := by
-- proof
  apply RayClassField.Modulus.dvd_lcm_left 𝔪₁ 𝔪₂

/--
[Modulus.dvd_lcm_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop226.lean)
-/
@[path]
private lemma dvd_lcm_right_eq
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪₁ 𝔪₂ : Modulus K} :
-- imply
  𝔪₂.dvd (𝔪₁.lcm 𝔪₂) := by
-- proof
  apply RayClassField.Modulus.dvd_lcm_right 𝔪₁ 𝔪₂


-- created on 2026-10-23
