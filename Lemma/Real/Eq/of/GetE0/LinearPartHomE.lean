import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.Reflection.AffineWeylSemidirectMulEquiv
open Set AffineWeylGroup AffineWeylGroupFullData
open scoped InnerProductSpace


/--
[ext_of_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/AffineWeylSemidirectMulEquiv.lean)
-/
@[path]
private lemma ext_of_decomp
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {d : AffineWeylSemidirectData E}
  {g₁ g₂ : ↥d.affineWeylSubgroup}
-- given
  (hlin : linearPartHom (g₁ : AffineIsometryEquiv ℝ E E) = linearPartHom (g₂ : AffineIsometryEquiv ℝ E E))
  (htrans : (g₁ : AffineIsometryEquiv ℝ E E) 0 = (g₂ : AffineIsometryEquiv ℝ E E) 0) :
-- imply
  g₁ = g₂ := by
-- proof
  ext x : 2
  rw [d.affine_decomp g₁ g₁.prop x, d.affine_decomp g₂ g₂.prop x, hlin, htrans]


namespace AffineWeylGroup

/--
[reflections_generate_affineWeylGroup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/AffineWeylSemidirectMulEquiv.lean)
-/
@[path]
private lemma reflections_generate_affineWeylGroup
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {Wa : AffineWeylGroup E} :
-- imply
  Subgroup.closure Wa.affineReflections = Wa.reflGroup.group :=
-- proof
  Wa.reflGroup.generated_by_reflections.symm

end AffineWeylGroup


namespace AffineWeylGroupFullData

/--
[coroot_translation_is_product_of_reflections](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/AffineWeylSemidirectMulEquiv.lean)
-/
@[path]
private lemma coroot_translation_is_product_of_reflections
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {d : AffineWeylGroupFullData E}
  {α : E}
-- given
  (hα : α ∈ d.roots) :
-- imply
  ∀ v : E, v + d.coroot α = d.affineReflFun α 1 (d.affineReflFun α 0 v) := by
-- proof
  intro v
  set c := d.coroot α
  have hc : ⟪α, c⟫_ℝ = 2 := by
    simp only [c]
    rw [d.coroot_def α hα, inner_smul_right, div_mul_cancel₀]
    exact inner_self_ne_zero.mpr (d.roots_ne_zero α hα)
  simp only [affineReflFun, Int.cast_zero, Int.cast_one, sub_zero]
  have hw : ⟪α, v - ⟪α, v⟫_ℝ • c⟫_ℝ = -⟪α, v⟫_ℝ := by
    simp [inner_sub_right, inner_smul_right, hc]
    ring
  rw [hw]
  module

end AffineWeylGroupFullData


-- created on 2026-10-23
-- updated on 2026-10-24
