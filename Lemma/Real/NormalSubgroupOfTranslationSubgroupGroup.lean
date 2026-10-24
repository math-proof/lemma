import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.AffineCoxeter.SemidirectProduct
open Set AffineReflectionGroup
open scoped InnerProductSpace


namespace AffineReflectionGroup

/--
[translationSubgroup_normal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/SemidirectProduct.lean)
-/
@[path]
private lemma translationSubgroup_normal
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {W : AffineReflectionGroup E} :
-- imply
  (W.TranslationSubgroup.subgroupOf W.group).Normal := by
-- proof
  constructor
  intro ⟨n, hn_W⟩ hn_mem ⟨g, hg_W⟩
  simp only [Subgroup.mem_subgroupOf] at hn_mem ⊢
  simp only [AffineReflectionGroup.TranslationSubgroup, Subgroup.mem_inf,
    MonoidHom.mem_ker] at hn_mem ⊢
  exact ⟨W.group.mul_mem (W.group.mul_mem hg_W hn_W) (W.group.inv_mem hg_W),
    by simp [hn_mem.2]⟩

end AffineReflectionGroup

namespace AffineReflectionGroup

/--
[stabilizer_le_group](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/SemidirectProduct.lean)
-/
@[path]
private lemma stabilizer_le_group
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {W : AffineReflectionGroup E}
  {x : E} :
-- imply
  W.Stabilizer x ≤ W.group :=
-- proof
  fun _ hg => hg.1

end AffineReflectionGroup

namespace AffineReflectionGroup

/--
[stabilizer_surjects_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/SemidirectProduct.lean)
-/
@[path]
private lemma stabilizer_surjects_unconditional
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {W : AffineReflectionGroup E}
  {x : E}
-- given
  (hx : W.SpecialPoint x) :
-- imply
  ∀ wbar ∈ W.LinearPartGroup, ∃ g ∈ W.Stabilizer x, linearPartHom g = wbar := by
-- proof
  intro wbar hwbar
  set R := {s : AffineIsometryEquiv ℝ E E | s ∈ W.group ∧ ∃ η ∈ W.arrangement.hyperplanes,
    (∀ y ∈ η.carrier, s y = y) ∧ s * s = 1} with hR_def
  set S_img := (W.Stabilizer x).map linearPartHom with hS_img_def
  suffices wbar ∈ S_img by
    obtain ⟨g, hg, rfl⟩ := this
    exact ⟨g, hg, rfl⟩
  have hLinPart : W.LinearPartGroup = Subgroup.closure (linearPartHom '' R) := by
    unfold LinearPartGroup
    rw [W.generated_by_reflections]
    exact MonoidHom.map_closure linearPartHom R
  rw [hLinPart] at hwbar
  apply (Subgroup.closure_le S_img).mpr _ hwbar
  rintro _ ⟨s, ⟨hs_group, η, hη_arr, h_fix, h_inv⟩, rfl⟩
  obtain ⟨η', hη'_arr, ⟨t, h_par⟩, hx_carrier⟩ := hx η hη_arr
  obtain ⟨s', hs'_group, h_fix', h_inv', _⟩ := W.has_reflection η' hη'_arr
  have hs'_stab : s' ∈ W.Stabilizer x := ⟨hs'_group, h_fix' x hx_carrier⟩
  have ht_ne : t ≠ 0 := by
    intro ht0
    have : η'.normal = (0 : ℝ) • η.normal := by rw [← ht0, h_par]
    simp at this
    exact η'.normal_ne_zero this
  have h_par_rev : ∃ t' : ℝ, η.normal = t' • η'.normal := by
    refine ⟨1/t, ?_⟩
    rw [h_par, smul_smul, one_div, inv_mul_cancel₀ ht_ne, one_smul]
  have h_same_lin : linearPartHom s' = linearPartHom s :=
    W.parallel_reflections_same_linear_part s' hs'_group s hs_group
      η' hη'_arr η hη_arr h_fix' h_inv' h_fix h_inv h_par_rev
  rw [← h_same_lin]
  exact ⟨s', hs'_stab, rfl⟩

end AffineReflectionGroup

namespace AffineReflectionGroup

/--
[semidirect_product_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/SemidirectProduct.lean)
-/
@[path]
private lemma semidirect_product_decomposition
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {W : AffineReflectionGroup E}
  {x : E}
-- given
  (hgen : ∀ wbar ∈ W.LinearPartGroup, ∃ g ∈ W.Stabilizer x, linearPartHom g = wbar) :
-- imply
  ∀ w ∈ W.group, ∃ t ∈ W.TranslationSubgroup, ∃ s ∈ W.Stabilizer x, w = t * s := by
-- proof
  intro w hw
  have hw_lin : linearPartHom w ∈ W.LinearPartGroup := ⟨w, hw, rfl⟩
  obtain ⟨s, hs_stab, hs_lin⟩ := hgen _ hw_lin
  refine ⟨w * s⁻¹, ?_, s, hs_stab, ?_⟩
  ·
    constructor
    · exact W.group.mul_mem hw (W.group.inv_mem (stabilizer_le_group hs_stab))
    ·
      show w * s⁻¹ ∈ linearPartHom.ker
      rw [MonoidHom.mem_ker, map_mul, map_inv, hs_lin, mul_inv_cancel]
  · group

end AffineReflectionGroup

namespace AffineReflectionGroup

/--
[semidirect_product_decomposition_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/SemidirectProduct.lean)
-/
@[path]
private lemma semidirect_product_decomposition_unconditional
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {W : AffineReflectionGroup E}
  {x : E}
-- given
  (hx : W.SpecialPoint x) :
-- imply
  ∀ w ∈ W.group, ∃ t ∈ W.TranslationSubgroup, ∃ s ∈ W.Stabilizer x, w = t * s :=
-- proof
  semidirect_product_decomposition (stabilizer_surjects_unconditional hx)

end AffineReflectionGroup


-- created on 2026-10-24
