import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.Lec7ClosedProductSubvariety
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Lec7ClosedProductSubvariety


namespace Lec7ClosedProductSubvariety

/--
[lemma16_tensorProduct_map_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec7ClosedProductSubvariety.lean)
-/
@[path]
lemma lemma16_tensorProduct_map_surjective
  [CommSemiring R]
  [AddCommMonoid M]
  [Module R M]
  [AddCommMonoid N]
  [Module R N]
  [AddCommMonoid M']
  [Module R M']
  [AddCommMonoid N']
  [Module R N']
  {f : M →ₗ[R] M'}
  {g : N →ₗ[R] N'}
-- given
  (hf : Function.Surjective f)
  (hg : Function.Surjective g) :
-- imply
  Function.Surjective (TensorProduct.map f g) :=
-- proof
  TensorProduct.map_surjective hf hg

end Lec7ClosedProductSubvariety

namespace Lec7ClosedProductSubvariety

/--
[lemma16_algebra_tensorProduct_map_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec7ClosedProductSubvariety.lean)
-/
@[path]
lemma lemma16_algebra_tensorProduct_map_surjective
  [CommSemiring R]
  [CommSemiring A₁]
  [CommSemiring B₁]
  [CommSemiring A₂]
  [CommSemiring B₂]
  [Algebra R A₁]
  [Algebra R B₁]
  [Algebra R A₂]
  [Algebra R B₂]
  {φ : A₁ →ₐ[R] B₁}
  {ψ : A₂ →ₐ[R] B₂}
-- given
  (hφ : Function.Surjective φ)
  (hψ : Function.Surjective ψ) :
-- imply
  Function.Surjective (Algebra.TensorProduct.map φ ψ) :=
-- proof
  TensorProduct.map_surjective hφ hψ

end Lec7ClosedProductSubvariety

namespace Lec7ClosedProductSubvariety

/--
[lemma16_closed_product_subvariety](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec7ClosedProductSubvariety.lean)
-/
@[path]
lemma lemma16_closed_product_subvariety
  {X₁ X₂ Y₁ Y₂ : Scheme}
  {i₁ : X₁ ⟶ Y₁}
  {i₂ : X₂ ⟶ Y₂}
  [IsClosedImmersion i₁]
  [IsClosedImmersion i₂] :
-- imply
  IsClosedImmersion (Limits.prod.map i₁ i₂) := by
-- proof
  have h_eq : Limits.prod.map i₁ i₂ =
    Limits.prod.map i₁ (𝟙 X₂) ≫ Limits.prod.map (𝟙 Y₁) i₂ := by
    simp [Limits.prod.map_map]
  rw [h_eq]
  exact IsClosedImmersion.comp _ _

end Lec7ClosedProductSubvariety


-- created on 2026-10-23
