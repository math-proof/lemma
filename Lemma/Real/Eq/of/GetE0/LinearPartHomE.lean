import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.Reflection.AffineWeylSemidirectMulEquiv
import Lemma.Matrix.Eq.of.Offset.Normal.AffineHyperplaneE
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


/--
[toSemidirect_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/AffineWeylSemidirectMulEquiv.lean)
-/
@[path]
private lemma toSemidirect_injective
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {d : AffineWeylSemidirectData E} :
-- imply
  Function.Injective d.toSemidirect := by
-- proof
  exact AffineWeylSemidirectData.toSemidirect_injective


/--
[toSemidirect_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/AffineWeylSemidirectMulEquiv.lean)
-/
@[path]
private lemma toSemidirect_surjective
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {d : AffineWeylSemidirectData E} :
-- imply
  Function.Surjective d.toSemidirect := by
-- proof
  exact AffineWeylSemidirectData.toSemidirect_surjective


/--
[toSemidirect_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/AffineWeylSemidirectMulEquiv.lean)
-/
@[path]
private lemma toSemidirect_mul
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {d : AffineWeylSemidirectData E}
  {g₁ g₂ : ↥d.affineWeylSubgroup} :
-- imply
  d.toSemidirect (g₁ * g₂) = d.toSemidirect g₁ * d.toSemidirect g₂ := by
-- proof
  exact AffineWeylSemidirectData.toSemidirect_mul g₁ g₂



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
  Subgroup.closure (Wa.affineReflections) = Wa.reflGroup.group :=
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
  ∀ v : E, v + d.coroot α = d.affineReflFun α 1 (d.affineReflFun α 0 v) :=
-- proof
  AffineWeylGroupFullData.corootTranslation_eq_comp_affineRefls hα

end AffineWeylGroupFullData


-- created on 2026-10-23
-- updated on 2026-10-24
