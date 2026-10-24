import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.NumberTheoryI.code.Cor227
open RayClassField
open scoped NumberField


namespace RayClassField

/--
[Modulus.dvd_trans'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor227.lean)
-/
@[path]
lemma Modulus.dvd_trans'
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪₁ 𝔪₂ 𝔪₃ : Modulus K}
-- given
  (h₁₂ : 𝔪₁.dvd 𝔪₂)
  (h₂₃ : 𝔪₂.dvd 𝔪₃) :
-- imply
  𝔪₁.dvd 𝔪₃ :=
-- proof
  fun v => le_trans (h₁₂ v) (h₂₃ v)

end RayClassField

namespace RayClassField

/--
[Modulus.dvd_refl](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor227.lean)
-/
@[path]
lemma Modulus.dvd_refl
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪 : Modulus K} :
-- imply
  𝔪.dvd 𝔪 :=
-- proof
  fun _ => le_refl _

end RayClassField

namespace RayClassField

/--
[CongruenceSubgroupPair.isEquiv_refl](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor227.lean)
-/
@[path]
lemma CongruenceSubgroupPair.isEquiv_refl
  {K : Type u}
  [Field K]
  [NumberField K]
  {p : CongruenceSubgroupPair K} :
-- imply
  p.IsEquiv p :=
-- proof
  rfl

end RayClassField

namespace RayClassField

/--
[CongruenceSubgroupPair.IsEquiv.symm'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor227.lean)
-/
@[path]
lemma CongruenceSubgroupPair.IsEquiv.symm'
  {K : Type u}
  [Field K]
  [NumberField K]
  {p₁ p₂ : CongruenceSubgroupPair K}
-- given
  (h : p₁.IsEquiv p₂) :
-- imply
  p₂.IsEquiv p₁ :=
-- proof
  h.symm

end RayClassField

namespace RayClassField

/--
[CongruenceSubgroupPair.IsEquiv.trans_of_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor227.lean)
-/
@[path]
lemma CongruenceSubgroupPair.IsEquiv.trans_of_dvd
  {K : Type u}
  [Field K]
  [NumberField K]
  {K : Type u}
  [Field K]
  [NumberField K]
  {p₁ p₂ p₃ : CongruenceSubgroupPair K}
-- given
  (h₁₂ : p₁.IsEquiv p₂)
  (h₂₃ : p₂.IsEquiv p₃)
  (hdvd₁ : p₂.modulus.dvd p₁.modulus)
  (hdvd₃ : p₂.modulus.dvd p₃.modulus) :
-- imply
  p₁.IsEquiv p₃ := by
-- proof
  have hA₁_le_A₂ : FracIdealsCoprime_subgroup K p₁.modulus ≤
    FracIdealsCoprime_subgroup K p₂.modulus :=
    FracIdealsCoprime_subgroup_mono hdvd₁
  have hA₃_le_A₂ : FracIdealsCoprime_subgroup K p₃.modulus ≤
    FracIdealsCoprime_subgroup K p₂.modulus :=
    FracIdealsCoprime_subgroup_mono hdvd₃
  show FracIdealsCoprime_subgroup K p₁.modulus ⊓ p₃.toAmbientSubgroup =
    FracIdealsCoprime_subgroup K p₃.modulus ⊓ p₁.toAmbientSubgroup
  ext x
  simp only [Subgroup.mem_inf]
  constructor
  · intro ⟨hxA₁, hxB₃⟩
    have hxA₃ := p₃.toAmbientSubgroup_le hxB₃
    have hxA₂ := hA₁_le_A₂ hxA₁
    have hxB₂ := (Subgroup.mem_inf.mp (h₂₃ ▸ Subgroup.mem_inf.mpr ⟨hxA₂, hxB₃⟩)).2
    have hxB₁ := (Subgroup.mem_inf.mp (h₁₂ ▸ Subgroup.mem_inf.mpr ⟨hxA₁, hxB₂⟩)).2
    exact ⟨hxA₃, hxB₁⟩
  · intro ⟨hxA₃, hxB₁⟩
    have hxA₁ := p₁.toAmbientSubgroup_le hxB₁
    have hxA₂ := hA₃_le_A₂ hxA₃
    have hxB₂ := (Subgroup.mem_inf.mp (h₁₂.symm ▸ Subgroup.mem_inf.mpr ⟨hxA₂, hxB₁⟩)).2
    have hxB₃ := (Subgroup.mem_inf.mp (h₂₃.symm ▸ Subgroup.mem_inf.mpr ⟨hxA₃, hxB₂⟩)).2
    exact ⟨hxA₁, hxB₃⟩

end RayClassField

namespace RayClassField

/--
[isEquiv_chain](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor227.lean)
-/
@[path]
lemma isEquiv_chain
  {K : Type u}
  [Field K]
  [NumberField K]
  {K : Type u}
  [Field K]
  [NumberField K]
  {p₁ p₂ p₃ : CongruenceSubgroupPair K}
-- given
  (h₁₂ : p₁.IsEquiv p₂)
  (h₂₃ : p₂.IsEquiv p₃)
  (hdvd₁₂ : p₂.modulus.dvd p₁.modulus)
  (hdvd₂₃ : p₃.modulus.dvd p₂.modulus) :
-- imply
  p₁.IsEquiv p₃ := by
-- proof
  have hA₁_le_A₂ : FracIdealsCoprime_subgroup K p₁.modulus ≤
    FracIdealsCoprime_subgroup K p₂.modulus :=
    FracIdealsCoprime_subgroup_mono hdvd₁₂
  have _hA₂_le_A₃ : FracIdealsCoprime_subgroup K p₂.modulus ≤
    FracIdealsCoprime_subgroup K p₃.modulus :=
    FracIdealsCoprime_subgroup_mono hdvd₂₃
  show FracIdealsCoprime_subgroup K p₁.modulus ⊓ p₃.toAmbientSubgroup =
    FracIdealsCoprime_subgroup K p₃.modulus ⊓ p₁.toAmbientSubgroup
  ext x
  simp only [Subgroup.mem_inf]
  constructor
  · intro ⟨hxA₁, hxB₃⟩
    have hxA₂ := hA₁_le_A₂ hxA₁
    have hxB₂ := (Subgroup.mem_inf.mp (h₂₃ ▸ Subgroup.mem_inf.mpr ⟨hxA₂, hxB₃⟩)).2
    have hxB₁ := (Subgroup.mem_inf.mp (h₁₂ ▸ Subgroup.mem_inf.mpr ⟨hxA₁, hxB₂⟩)).2
    exact ⟨p₃.toAmbientSubgroup_le hxB₃, hxB₁⟩
  · intro ⟨hxA₃, hxB₁⟩
    have hxA₁ := p₁.toAmbientSubgroup_le hxB₁
    have hxA₂ := hA₁_le_A₂ hxA₁
    have hxB₂ := (Subgroup.mem_inf.mp (h₁₂.symm ▸ Subgroup.mem_inf.mpr ⟨hxA₂, hxB₁⟩)).2
    have hxB₃ := (Subgroup.mem_inf.mp (h₂₃.symm ▸ Subgroup.mem_inf.mpr ⟨hxA₃, hxB₂⟩)).2
    exact ⟨hxA₁, hxB₃⟩

end RayClassField

namespace RayClassField

/--
[IsRayGenerator_of_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor227.lean)
-/
@[path]
lemma IsRayGenerator_of_dvd
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪₁ 𝔪₂ : Modulus K}
  {I : FracIdealsCoprime K 𝔪₂}
-- given
  (h : 𝔪₁.dvd 𝔪₂)
  (hI : IsRayGenerator 𝔪₂ I) :
-- imply
  IsRayGenerator 𝔪₁ (Subgroup.inclusion (FracIdealsCoprime_subgroup_mono h) I) := by
-- proof
  obtain ⟨α, hprinc, hcong, hsign⟩ := hI
  refine ⟨α, ?_, ?_, ?_⟩
  · simp only [Subgroup.coe_inclusion]
    exact hprinc
  · intro v hv
    have hv_n : 𝔪₂ (Place.finite v) ≠ 0 := by
      intro h0; exact hv (Nat.eq_zero_of_le_zero (h0 ▸ h (Place.finite v)))
    have hle : (𝔪₁ (Place.finite v) : ℤ) ≤ (𝔪₂ (Place.finite v) : ℤ) :=
      Int.ofNat_le.mpr (h (Place.finite v))
    calc v.valuation K ((α : K) - 1)
      ≤ ↑(Multiplicative.ofAdd (-(𝔪₂ (Place.finite v) : ℤ))) := hcong v hv_n
      _ ≤ ↑(Multiplicative.ofAdd (-(𝔪₁ (Place.finite v) : ℤ))) := by
        simp only [WithZero.coe_le_coe, Multiplicative.ofAdd_le]
        linarith
  · intro w hw
    exact hsign w (fun h0 => hw (Nat.eq_zero_of_le_zero (h0 ▸ h (Place.infinite w))))

end RayClassField

namespace RayClassField

/--
[RayGroup_inclusion_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor227.lean)
-/
@[path]
lemma RayGroup_inclusion_le
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪₁ 𝔪₂ : Modulus K}
-- given
  (h : 𝔪₁.dvd 𝔪₂) :
-- imply
  ∀ x : FracIdealsCoprime K 𝔪₂, x ∈ RayGroup K 𝔪₂ → (Subgroup.inclusion (FracIdealsCoprime_subgroup_mono h)) x ∈ RayGroup K 𝔪₁ := by
-- proof
  intro x hx
  let f : FracIdealsCoprime K 𝔪₂ →* FracIdealsCoprime K 𝔪₁ :=
    Subgroup.inclusion (FracIdealsCoprime_subgroup_mono h)
  suffices hsuff : Subgroup.map f (RayGroup K 𝔪₂) ≤ RayGroup K 𝔪₁ from
    hsuff ⟨x, hx, rfl⟩
  have hrw : Subgroup.map f (RayGroup K 𝔪₂) =
    Subgroup.closure (f '' {I | IsRayGenerator 𝔪₂ I}) :=
    MonoidHom.map_closure f {I | IsRayGenerator 𝔪₂ I}
  rw [hrw]
  apply Subgroup.closure_mono
  rintro _ ⟨I, hI, rfl⟩
  exact IsRayGenerator_of_dvd 𝔪₁ 𝔪₂ h I hI

end RayClassField

namespace RayClassField

/--
[RayGroup_toAmbientSubgroup_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor227.lean)
-/
@[path]
lemma RayGroup_toAmbientSubgroup_antitone
  {K : Type u}
  [Field K]
  [NumberField K]
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪₁ 𝔪₂ : Modulus K}
-- given
  (h : 𝔪₁.dvd 𝔪₂) :
-- imply
  RayGroup.toAmbientSubgroup K 𝔪₂ ≤ RayGroup.toAmbientSubgroup K 𝔪₁ := by
-- proof
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  let y₁ := Subgroup.inclusion (FracIdealsCoprime_subgroup_mono h) y
  have hy₁ : y₁ ∈ RayGroup K 𝔪₁ := RayGroup_inclusion_le 𝔪₁ 𝔪₂ h y hy
  apply Subgroup.mem_map.mpr
  exact ⟨y₁, hy₁, by simp only [Subgroup.subtype_apply]; rfl⟩

end RayClassField

namespace RayClassField

/--
[trans_of_dvd_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor227.lean)
-/
@[path]
lemma trans_of_dvd_reverse
  {K : Type u}
  [Field K]
  [NumberField K]
  {K : Type u}
  [Field K]
  [NumberField K]
  {p₁ p₂ p₃ : CongruenceSubgroupPair K}
-- given
  (h₁₂ : p₁.IsEquiv p₂)
  (h₂₃ : p₂.IsEquiv p₃)
  (hdvd₁ : p₁.modulus.dvd p₂.modulus)
  (hdvd₃ : p₃.modulus.dvd p₂.modulus) :
-- imply
  p₁.IsEquiv p₃ := by
-- proof
  let 𝔪₁ := p₁.modulus
  let 𝔪₂ := p₂.modulus
  let 𝔪₃ := p₃.modulus
  let 𝔪₁₃ := 𝔪₁.lcm 𝔪₃
  have hdvd_lcm₁ : 𝔪₁.dvd 𝔪₁₃ := Modulus.dvd_lcm_left 𝔪₁ 𝔪₃
  have hdvd_lcm₃ : 𝔪₃.dvd 𝔪₁₃ := Modulus.dvd_lcm_right 𝔪₁ 𝔪₃
  have hdvd_lcm_mid : 𝔪₁₃.dvd 𝔪₂ := fun v => max_le (hdvd₁ v) (hdvd₃ v)
  have hgcd_lcm : 𝔪₁₃.gcd 𝔪₂ = 𝔪₁₃ := by
    apply Modulus.dvd_antisymm'
    · exact Modulus.gcd_dvd_left 𝔪₁₃ 𝔪₂
    · intro v; exact le_min (le_refl _) (hdvd_lcm_mid v)
  have hA₂_le_A₁ : FracIdealsCoprime_subgroup K 𝔪₂ ≤ FracIdealsCoprime_subgroup K 𝔪₁ :=
    FracIdealsCoprime_subgroup_mono hdvd₁
  have hA₂_le_A₃ : FracIdealsCoprime_subgroup K 𝔪₂ ≤ FracIdealsCoprime_subgroup K 𝔪₃ :=
    FracIdealsCoprime_subgroup_mono hdvd₃
  have hR₁₃_le_R₁ : RayGroup.toAmbientSubgroup K 𝔪₁₃ ≤ RayGroup.toAmbientSubgroup K 𝔪₁ :=
    RayGroup_toAmbientSubgroup_antitone K hdvd_lcm₁
  have hR₁₃_le_R₃ : RayGroup.toAmbientSubgroup K 𝔪₁₃ ≤ RayGroup.toAmbientSubgroup K 𝔪₃ :=
    RayGroup_toAmbientSubgroup_antitone K hdvd_lcm₃
  have hR₁₃_le_B₁ : RayGroup.toAmbientSubgroup K 𝔪₁₃ ≤ p₁.toAmbientSubgroup := by
    intro y hy
    have hyR₁ := hR₁₃_le_R₁ hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hyR₁
    exact Subgroup.mem_map.mpr ⟨z, p₁.ray_le hz, rfl⟩
  have hR₁₃_le_B₃ : RayGroup.toAmbientSubgroup K 𝔪₁₃ ≤ p₃.toAmbientSubgroup := by
    intro y hy
    have hyR₃ := hR₁₃_le_R₃ hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hyR₃
    exact Subgroup.mem_map.mpr ⟨z, p₃.ray_le hz, rfl⟩
  have hB₂_le_A₁ : p₂.toAmbientSubgroup ≤ FracIdealsCoprime_subgroup K 𝔪₁ :=
    le_trans p₂.toAmbientSubgroup_le hA₂_le_A₁
  have hB₂_le_A₃ : p₂.toAmbientSubgroup ≤ FracIdealsCoprime_subgroup K 𝔪₃ :=
    le_trans p₂.toAmbientSubgroup_le hA₂_le_A₃
  have h_A₂_B₁_eq_B₂ : FracIdealsCoprime_subgroup K 𝔪₂ ⊓ p₁.toAmbientSubgroup =
    p₂.toAmbientSubgroup := by
    rw [← h₁₂]
    exact inf_eq_right.mpr hB₂_le_A₁
  have h_A₂_B₃_eq_B₂ : FracIdealsCoprime_subgroup K 𝔪₂ ⊓ p₃.toAmbientSubgroup =
    p₂.toAmbientSubgroup := by
    rw [h₂₃]
    exact inf_eq_right.mpr hB₂_le_A₃
  have hB₂_le_B₁ : p₂.toAmbientSubgroup ≤ p₁.toAmbientSubgroup := by
    rw [← h_A₂_B₁_eq_B₂]; exact inf_le_right
  have hB₂_le_B₃ : p₂.toAmbientSubgroup ≤ p₃.toAmbientSubgroup := by
    rw [← h_A₂_B₃_eq_B₂]; exact inf_le_right
  have hA₁₃_decomp : FracIdealsCoprime_subgroup K 𝔪₁₃ ≤
    FracIdealsCoprime_subgroup K 𝔪₂ ⊔ RayGroup.toAmbientSubgroup K 𝔪₁₃ := by
    have h := theorem_8_5_coprime_decomp K 𝔪₁₃ 𝔪₂
    rw [hgcd_lcm] at h
    calc FracIdealsCoprime_subgroup K 𝔪₁₃
      ≤ (FracIdealsCoprime_subgroup K 𝔪₁₃ ⊓ FracIdealsCoprime_subgroup K 𝔪₂) ⊔
        (FracIdealsCoprime_subgroup K 𝔪₁₃ ⊓ RayGroup.toAmbientSubgroup K 𝔪₁₃) := h
      _ ≤ FracIdealsCoprime_subgroup K 𝔪₂ ⊔ RayGroup.toAmbientSubgroup K 𝔪₁₃ :=
        sup_le_sup inf_le_right inf_le_right
  have mem_A₁₃ : ∀ x : (FracIdeal K)ˣ,
    x ∈ FracIdealsCoprime_subgroup K 𝔪₁ →
    x ∈ FracIdealsCoprime_subgroup K 𝔪₃ →
    x ∈ FracIdealsCoprime_subgroup K 𝔪₁₃ := by
    intro x hxA₁ hxA₃ v hv
    change (𝔪₁.lcm 𝔪₃) (Place.finite v) ≠ 0 at hv
    unfold Modulus.lcm at hv
    dsimp only at hv
    obtain h | h := Nat.lt_or_ge (𝔪₁ (Place.finite v)) (𝔪₃ (Place.finite v))
    · exact hxA₃ v (by omega)
    · exact hxA₁ v (by omega)
  show FracIdealsCoprime_subgroup K 𝔪₁ ⊓ p₃.toAmbientSubgroup =
    FracIdealsCoprime_subgroup K 𝔪₃ ⊓ p₁.toAmbientSubgroup
  ext x
  simp only [Subgroup.mem_inf]
  constructor
  ·
    intro ⟨hxA₁, hxB₃⟩
    have hxA₃ := p₃.toAmbientSubgroup_le hxB₃
    refine ⟨hxA₃, ?_⟩
    have hxA₁₃ := mem_A₁₃ x hxA₁ hxA₃
    have hx_sup := hA₁₃_decomp hxA₁₃
    rw [Subgroup.mem_sup] at hx_sup
    obtain ⟨a, haA₂, b, hbR₁₃, hab⟩ := hx_sup
    have hbB₁ := hR₁₃_le_B₁ hbR₁₃
    have hbB₃ := hR₁₃_le_B₃ hbR₁₃
    have haB₃ : a ∈ p₃.toAmbientSubgroup := by
      have : a = x * b⁻¹ := by rw [← hab]; group
      rw [this]
      exact mul_mem hxB₃ (inv_mem hbB₃)
    have haB₂ : a ∈ p₂.toAmbientSubgroup := by
      rw [← h_A₂_B₃_eq_B₂]
      exact ⟨haA₂, haB₃⟩
    have haB₁ := hB₂_le_B₁ haB₂
    rw [← hab]
    exact mul_mem haB₁ hbB₁
  ·
    intro ⟨hxA₃, hxB₁⟩
    have hxA₁ := p₁.toAmbientSubgroup_le hxB₁
    refine ⟨hxA₁, ?_⟩
    have hxA₁₃ := mem_A₁₃ x hxA₁ hxA₃
    have hx_sup := hA₁₃_decomp hxA₁₃
    rw [Subgroup.mem_sup] at hx_sup
    obtain ⟨a, haA₂, b, hbR₁₃, hab⟩ := hx_sup
    have hbB₁ := hR₁₃_le_B₁ hbR₁₃
    have hbB₃ := hR₁₃_le_B₃ hbR₁₃
    have haB₁ : a ∈ p₁.toAmbientSubgroup := by
      have : a = x * b⁻¹ := by rw [← hab]; group
      rw [this]
      exact mul_mem hxB₁ (inv_mem hbB₁)
    have haB₂ : a ∈ p₂.toAmbientSubgroup := by
      rw [← h_A₂_B₁_eq_B₂]
      exact ⟨haA₂, haB₁⟩
    have haB₃ := hB₂_le_B₃ haB₂
    rw [← hab]
    exact mul_mem haB₃ hbB₃

end RayClassField

namespace RayClassField

/--
[CongruenceSubgroupPair.IsEquiv.trans'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor227.lean)
-/
@[path]
lemma CongruenceSubgroupPair.IsEquiv.trans'
  {K : Type u}
  [Field K]
  [NumberField K]
  {K : Type u}
  [Field K]
  [NumberField K]
  {p₁ p₂ p₃ : CongruenceSubgroupPair K}
-- given
  (h₁₂ : p₁.IsEquiv p₂)
  (h₂₃ : p₂.IsEquiv p₃) :
-- imply
  p₁.IsEquiv p₃ := by
-- proof
  obtain ⟨r, hr_mod, hr_p₁, hr_p₂⟩ := proposition_22_6 p₁ p₂ h₁₂
  obtain ⟨s, hs_mod, hs_p₂, hs_p₃⟩ := proposition_22_6 p₂ p₃ h₂₃
  have hr_dvd₁ : r.modulus.dvd p₁.modulus := by
    rw [hr_mod]; exact Modulus.gcd_dvd_left p₁.modulus p₂.modulus
  have hr_dvd₂ : r.modulus.dvd p₂.modulus := by
    rw [hr_mod]; exact Modulus.gcd_dvd_right p₁.modulus p₂.modulus
  have hs_dvd₂ : s.modulus.dvd p₂.modulus := by
    rw [hs_mod]; exact Modulus.gcd_dvd_left p₂.modulus p₃.modulus
  have hs_dvd₃ : s.modulus.dvd p₃.modulus := by
    rw [hs_mod]; exact Modulus.gcd_dvd_right p₂.modulus p₃.modulus
  have h_r_s : r.IsEquiv s :=
    trans_of_dvd_reverse hr_p₂.symm' hs_p₂ hr_dvd₂ hs_dvd₂
  obtain ⟨t, ht_mod, ht_r, ht_s⟩ := proposition_22_6 r s h_r_s
  have ht_dvd_r : t.modulus.dvd r.modulus := by
    rw [ht_mod]; exact Modulus.gcd_dvd_left r.modulus s.modulus
  have ht_dvd_s : t.modulus.dvd s.modulus := by
    rw [ht_mod]; exact Modulus.gcd_dvd_right r.modulus s.modulus
  have ht_dvd₁ : t.modulus.dvd p₁.modulus := Modulus.dvd_trans' ht_dvd_r hr_dvd₁
  have ht_dvd₃ : t.modulus.dvd p₃.modulus := Modulus.dvd_trans' ht_dvd_s hs_dvd₃
  have hp₁_t : p₁.IsEquiv t := isEquiv_chain hr_p₁ ht_r hr_dvd₁ ht_dvd_r
  have hp₃_t : p₃.IsEquiv t := isEquiv_chain hs_p₃ ht_s hs_dvd₃ ht_dvd_s
  exact hp₁_t.trans_of_dvd hp₃_t.symm' ht_dvd₁ ht_dvd₃

end RayClassField

/--
[Modulus.dvd_antisymm'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor227.lean)
-/
@[path]
private lemma dvd_antisymm'_eq
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪₁ 𝔪₂ : Modulus K}
-- given
  (h₁ : 𝔪₁.dvd 𝔪₂)
  (h₂ : 𝔪₂.dvd 𝔪₁) :
-- imply
  𝔪₁ = 𝔪₂ := by
-- proof
  apply RayClassField.Modulus.dvd_antisymm' h₁ h₂

/--
[Modulus.gcd_weight_lt_of_not_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor227.lean)
-/
@[path]
private lemma gcd_weight_lt_of_not_dvd_eq
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪₁ 𝔪₂ : Modulus K}
-- given
  (h : ¬ 𝔪₁.dvd 𝔪₂) :
-- imply
  (𝔪₁.gcd 𝔪₂).weight < 𝔪₁.weight := by
-- proof
  apply RayClassField.Modulus.gcd_weight_lt_of_not_dvd h

/--
[corollary_22_7_existence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor227.lean)
-/
@[path]
private lemma corollary_22_7_existence_eq
  {K : Type u}
  [Field K]
  [NumberField K]
  {p : CongruenceSubgroupPair K} :
-- imply
  ∃ p₀ : CongruenceSubgroupPair K, p.IsEquiv p₀ ∧ ∀ q : CongruenceSubgroupPair K, p.IsEquiv q → p₀.modulus.dvd q.modulus := by
-- proof
  apply RayClassField.corollary_22_7_existence p

/--
[corollary_22_7_modulus_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor227.lean)
-/
@[path]
private lemma corollary_22_7_modulus_unique_eq
  {K : Type u}
  [Field K]
  [NumberField K]
  {p p₀ p₀' : CongruenceSubgroupPair K}
-- given
  (hp₀ : p.IsEquiv p₀)
  (hp₀_min : ∀ q, p.IsEquiv q → p₀.modulus.dvd q.modulus)
  (hp₀' : p.IsEquiv p₀')
  (hp₀'_min : ∀ q, p.IsEquiv q → p₀'.modulus.dvd q.modulus) :
-- imply
  p₀.modulus = p₀'.modulus := by
-- proof
  apply RayClassField.corollary_22_7_modulus_unique p p₀ p₀' hp₀ hp₀_min hp₀' hp₀'_min

/--
[corollary_22_7](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor227.lean)
-/
@[path]
private lemma corollary_22_7_eq
  {K : Type u}
  [Field K]
  [NumberField K]
  {p : CongruenceSubgroupPair K} :
-- imply
  ∃! (𝔠 : Modulus K), (∃ p₀ : CongruenceSubgroupPair K, p₀.modulus = 𝔠 ∧ p.IsEquiv p₀) ∧ (∀ q : CongruenceSubgroupPair K, p.IsEquiv q → 𝔠.dvd q.modulus) := by
-- proof
  apply RayClassField.corollary_22_7 p


-- created on 2026-10-23
