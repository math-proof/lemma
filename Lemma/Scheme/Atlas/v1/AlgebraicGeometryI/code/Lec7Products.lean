import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.Lec7Products
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Lec7Products
open scoped TensorProduct


namespace Lec7Products

/--
[tensor_product_map_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec7Products.lean)
-/
@[path]
lemma tensor_product_map_surjective
  [CommRing R]
  [CommRing S]
  [Algebra R S]
  [Ring A]
  [Ring B]
  [Ring C]
  [Ring D]
  [Algebra R A]
  [Algebra R B]
  [Algebra R C]
  [Algebra R D]
  [Algebra S A]
  [Algebra S B]
  [IsScalarTower R S A]
  [IsScalarTower R S B]
  {f : A →ₐ[S] B}
  {g : C →ₐ[R] D}
-- given
  (hf : Function.Surjective f)
  (hg : Function.Surjective g) :
-- imply
  Function.Surjective (Algebra.TensorProduct.map f g) :=
-- proof
  Algebra.TensorProduct.map_surjective f g hf hg

end Lec7Products

namespace Lec7Products

/--
[isClosedImmersion_prod_map](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec7Products.lean)
-/
@[path]
lemma isClosedImmersion_prod_map
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

end Lec7Products

namespace Lec7Products

/--
[isProjective_of_closedImmersion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec7Products.lean)
-/
@[path]
lemma isProjective_of_closedImmersion
  {X Y : Scheme}
  {f : X ⟶ Y}
  [IsClosedImmersion f]
  [Scheme.IsProjective Y] :
-- imply
  Scheme.IsProjective X where exists_closedImmersion_into_proj := by
-- proof
  obtain ⟨A, σ, hcr, hsl, hasg, 𝒜, hgr, g, hg⟩ :=
    Scheme.IsProjective.exists_closedImmersion_into_proj (X := Y)
  exact ⟨A, σ, hcr, hsl, hasg, 𝒜, hgr, f ≫ g, IsClosedImmersion.comp f g⟩

end Lec7Products

namespace Lec7Products

/--
[segreAlgHom_X](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec7Products.lean)
-/
@[path]
lemma segreAlgHom_X
  {R : Type*}
  [CommRing R]
  {n m : ℕ}
  {i : Fin n}
  {j : Fin m} :
-- imply
  segreAlgHom R n m (MvPolynomial.X (i, j)) = MvPolynomial.X i ⊗ₜ[R] MvPolynomial.X j := by
-- proof
  simp [segreAlgHom, MvPolynomial.aeval_X]

end Lec7Products

namespace Lec7Products

/--
[segreAlgHom_relation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec7Products.lean)
-/
@[path]
lemma segreAlgHom_relation
  {R : Type*}
  [CommRing R]
  {n m : ℕ}
  {i k : Fin n}
  {j l : Fin m} :
-- imply
  segreAlgHom R n m (MvPolynomial.X (i, j) * MvPolynomial.X (k, l) - MvPolynomial.X (k, j) * MvPolynomial.X (i, l)) = 0 := by
-- proof
  simp only [map_sub, map_mul, segreAlgHom_X]
  simp only [Algebra.TensorProduct.tmul_mul_tmul]
  ring_nf

end Lec7Products

namespace Lec7Products

/--
[segreRelation_isHomogeneous](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec7Products.lean)
-/
@[path]
lemma segreRelation_isHomogeneous
  {R : Type*}
  [CommRing R]
  {n m : ℕ}
  {i k : Fin n}
  {j l : Fin m} :
-- imply
  letI := @MvPolynomial.gradedAlgebra (Fin n × Fin m) R _ (MvPolynomial.X (i, j) * MvPolynomial.X (k, l) - MvPolynomial.X (k, j) * MvPolynomial.X (i, l) : MvPolynomial (Fin n × Fin m) R).IsHomogeneous 2 := by
-- proof
  letI := @MvPolynomial.gradedAlgebra (Fin n × Fin m) R _
  apply MvPolynomial.IsHomogeneous.sub
  · exact (MvPolynomial.isHomogeneous_X _ _).mul (MvPolynomial.isHomogeneous_X _ _)
  · exact (MvPolynomial.isHomogeneous_X _ _).mul (MvPolynomial.isHomogeneous_X _ _)
/-- Lec 7, Prop 8: the product of two projective schemes is projective
(via the Segre embedding). -/
section Goal68

end Lec7Products

namespace Lec7Products

/--
[graphMorphism_fst](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec7Products.lean)
-/
@[path]
lemma graphMorphism_fst
  {X Y : Scheme}
  {f : X ⟶ Y} :
-- imply
  graphMorphism f ≫ Limits.prod.fst = 𝟙 X := by
-- proof
  simp [graphMorphism, prod.lift_fst]

end Lec7Products

namespace Lec7Products

/--
[graphMorphism_snd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec7Products.lean)
-/
@[path]
lemma graphMorphism_snd
  {X Y : Scheme}
  {f : X ⟶ Y} :
-- imply
  graphMorphism f ≫ Limits.prod.snd = f := by
-- proof
  simp [graphMorphism, prod.lift_snd]

end Lec7Products

namespace Lec7Products

/--
[graphMorphism_id](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec7Products.lean)
-/
@[path]
lemma graphMorphism_id
  {X : Scheme} :
-- imply
  graphMorphism (𝟙 X) = Limits.prod.lift (𝟙 X) (𝟙 X) := by
-- proof
  rfl

end Lec7Products


-- created on 2026-10-23
