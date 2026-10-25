import Mathlib
import sympy.Basic
import Def.v1.Atlas.NumberTheoryI.code.Lem225
open RayClassField
open scoped NumberField


namespace RayClassField

/--
[RayGroup.toAmbientSubgroup_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Lem225.lean)
-/
@[path]
lemma RayGroup.toAmbientSubgroup_le
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪 : Modulus K} :
-- imply
  RayGroup.toAmbientSubgroup K 𝔪 ≤ FracIdealsCoprime_subgroup K 𝔪 := by
-- proof
  intro x hx
  obtain ⟨y, _, rfl⟩ := Subgroup.mem_map.mp hx
  exact y.prop

end RayClassField

namespace RayClassField

/--
[FracIdealsCoprime_subgroup_mono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Lem225.lean)
-/
@[path]
lemma FracIdealsCoprime_subgroup_mono
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪₁ 𝔪₂ : Modulus K}
-- given
  (h : 𝔪₂.dvd 𝔪₁) :
-- imply
  FracIdealsCoprime_subgroup K 𝔪₁ ≤ FracIdealsCoprime_subgroup K 𝔪₂ := by
-- proof
  intro I hI v hv
  exact hI v (fun h0 => hv (by
    have := h (Place.finite v)
    omega))

end RayClassField

namespace RayClassField

/--
[CongruenceSubgroupPair.toAmbientSubgroup_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Lem225.lean)
-/
@[path]
lemma CongruenceSubgroupPair.toAmbientSubgroup_le
  {K : Type u}
  [Field K]
  [NumberField K]
  {p : CongruenceSubgroupPair K} :
-- imply
  p.toAmbientSubgroup ≤ FracIdealsCoprime_subgroup K p.modulus := by
-- proof
  intro x hx
  obtain ⟨y, _, rfl⟩ := Subgroup.mem_map.mp hx
  exact y.prop

end RayClassField

namespace RayClassField

/--
[lemma_22_5_necessity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Lem225.lean)
-/
@[path]
lemma lemma_22_5_necessity
  {K : Type u}
  [Field K]
  [NumberField K]
  {p₁ p₂ : CongruenceSubgroupPair K}
-- given
  (_hdvd : p₂.modulus.dvd p₁.modulus)
  (hequiv : p₁.IsEquiv p₂) :
-- imply
  FracIdealsCoprime_subgroup K p₁.modulus ⊓ RayGroup.toAmbientSubgroup K p₂.modulus ≤ p₁.toAmbientSubgroup := by
-- proof
  have hR₂_le_C₂ : RayGroup.toAmbientSubgroup K p₂.modulus ≤ p₂.toAmbientSubgroup := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_map.mpr ⟨y, p₂.ray_le hy, rfl⟩
  intro x ⟨hx_I₁, hx_R₂⟩
  have hx_C₂ : x ∈ p₂.toAmbientSubgroup := hR₂_le_C₂ hx_R₂
  have hmem : x ∈ FracIdealsCoprime_subgroup K p₁.modulus ⊓ p₂.toAmbientSubgroup :=
    ⟨hx_I₁, hx_C₂⟩
  rwa [hequiv] at hmem

end RayClassField

namespace RayClassField

/--
[lemma_22_5_sufficiency](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Lem225.lean)
-/
@[path]
lemma lemma_22_5_sufficiency
  {K : Type u}
  [Field K]
  [NumberField K]
  {p₁ : CongruenceSubgroupPair K}
  {𝔪₂ : Modulus K}
-- given
  (hdvd : 𝔪₂.dvd p₁.modulus)
  (hcond : FracIdealsCoprime_subgroup K p₁.modulus ⊓ RayGroup.toAmbientSubgroup K 𝔪₂ ≤ p₁.toAmbientSubgroup) :
-- imply
  ∃ p₂ : CongruenceSubgroupPair K, p₂.modulus = 𝔪₂ ∧ p₁.IsEquiv p₂ ∧ p₂.toAmbientSubgroup = p₁.toAmbientSubgroup ⊔ RayGroup.toAmbientSubgroup K 𝔪₂ := by
-- proof
  have hC₁_le_I₁ : p₁.toAmbientSubgroup ≤ FracIdealsCoprime_subgroup K p₁.modulus :=
    p₁.toAmbientSubgroup_le
  have hI₁_le_I₂ : FracIdealsCoprime_subgroup K p₁.modulus ≤
    FracIdealsCoprime_subgroup K 𝔪₂ :=
    FracIdealsCoprime_subgroup_mono hdvd
  have hC₁_le_I₂ : p₁.toAmbientSubgroup ≤ FracIdealsCoprime_subgroup K 𝔪₂ :=
    le_trans hC₁_le_I₁ hI₁_le_I₂
  have hR₂_le_I₂ : RayGroup.toAmbientSubgroup K 𝔪₂ ≤ FracIdealsCoprime_subgroup K 𝔪₂ :=
    RayGroup.toAmbientSubgroup_le 𝔪₂
  have hprod_le_I₂ : p₁.toAmbientSubgroup ⊔ RayGroup.toAmbientSubgroup K 𝔪₂ ≤
    FracIdealsCoprime_subgroup K 𝔪₂ :=
    sup_le hC₁_le_I₂ hR₂_le_I₂
  have hR₂_le_prod : RayGroup.toAmbientSubgroup K 𝔪₂ ≤
    p₁.toAmbientSubgroup ⊔ RayGroup.toAmbientSubgroup K 𝔪₂ :=
    le_sup_right
  let C₂_ambient := p₁.toAmbientSubgroup ⊔ RayGroup.toAmbientSubgroup K 𝔪₂
  let C₂_sub : Subgroup (FracIdealsCoprime K 𝔪₂) :=
    C₂_ambient.comap (FracIdealsCoprime_subgroup K 𝔪₂).subtype
  have hray_le : RayGroup K 𝔪₂ ≤ C₂_sub := by
    intro x hx
    show (FracIdealsCoprime_subgroup K 𝔪₂).subtype x ∈ C₂_ambient
    exact hR₂_le_prod (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  let p₂ : CongruenceSubgroupPair K :=
    { modulus := 𝔪₂
      subgroup := C₂_sub
      ray_le := hray_le }
  have himage : p₂.toAmbientSubgroup = C₂_ambient := by
    ext x
    simp only [CongruenceSubgroupPair.toAmbientSubgroup, Subgroup.mem_map, Subtype.exists]
    constructor
    · rintro ⟨x', hx'_mem, hx'_C₂, rfl⟩
      exact hx'_C₂
    · intro hx
      have hx_I₂ : x ∈ FracIdealsCoprime_subgroup K 𝔪₂ := hprod_le_I₂ hx
      exact ⟨x, hx_I₂, hx, rfl⟩
  have hequiv : p₁.IsEquiv p₂ := by
    show FracIdealsCoprime_subgroup K p₁.modulus ⊓ p₂.toAmbientSubgroup =
      FracIdealsCoprime_subgroup K 𝔪₂ ⊓ p₁.toAmbientSubgroup
    rw [himage]
    have hRHS : FracIdealsCoprime_subgroup K 𝔪₂ ⊓ p₁.toAmbientSubgroup = p₁.toAmbientSubgroup := by
      exact inf_eq_right.mpr hC₁_le_I₂
    rw [hRHS]
    rw [inf_comm]
    rw [sup_inf_assoc_of_le _ hC₁_le_I₁]
    rw [sup_eq_left.mpr]
    rwa [inf_comm]
  exact ⟨p₂, rfl, hequiv, himage⟩

end RayClassField

namespace RayClassField

/--
[lemma_22_5](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Lem225.lean)
-/
@[path]
lemma lemma_22_5
  {K : Type u}
  [Field K]
  [NumberField K]
  {p₁ : CongruenceSubgroupPair K}
  {𝔪₂ : Modulus K}
-- given
  (hdvd : 𝔪₂.dvd p₁.modulus) :
-- imply
  (∃ p₂ : CongruenceSubgroupPair K, p₂.modulus = 𝔪₂ ∧ p₁.IsEquiv p₂) ↔ FracIdealsCoprime_subgroup K p₁.modulus ⊓ RayGroup.toAmbientSubgroup K 𝔪₂ ≤ p₁.toAmbientSubgroup := by
-- proof
  constructor
  ·
    rintro ⟨p₂, hmod, hequiv⟩
    rw [← hmod]
    exact lemma_22_5_necessity p₁ p₂ (by rwa [hmod]) hequiv
  ·
    intro hcond
    obtain ⟨p₂, hmod, hequiv, _⟩ := lemma_22_5_sufficiency p₁ 𝔪₂ hdvd hcond
    exact ⟨p₂, hmod, hequiv⟩

end RayClassField


-- created on 2026-10-23
