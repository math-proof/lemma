/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec7Products.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous

set_option maxHeartbeats 400000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Lec7Products

section Goal62

/-- Product of a closed immersion with the identity on the right is a
closed immersion (Lec 7, used for Prop 8). -/
noncomputable instance isClosedImmersion_prod_map_id_right
    {X₁ Y₁ Z : Scheme} (f : X₁ ⟶ Y₁) [IsClosedImmersion f] :
    IsClosedImmersion (Limits.prod.map f (𝟙 Z)) :=
  IsClosedImmersion.isStableUnderBaseChange.of_isPullback
    (IsPullback.of_prod_fst_with_id f Z) ‹_›

/-- Product of the identity on the left with a closed immersion is a
closed immersion (Lec 7, used for Prop 8). -/
noncomputable instance isClosedImmersion_prod_map_id_left
    {X₂ Y₂ Z : Scheme} (g : X₂ ⟶ Y₂) [IsClosedImmersion g] :
    IsClosedImmersion (Limits.prod.map (𝟙 Z) g) := by
  have h_eq : Limits.prod.map (𝟙 Z) g =
    (Limits.prod.braiding Z X₂).hom ≫ Limits.prod.map g (𝟙 Z) ≫
    (Limits.prod.braiding Y₂ Z).hom := by
    apply prod.hom_ext
    all_goals simp [prod.braiding_hom, prod.lift_fst, prod.lift_snd, prod.map_fst,
      prod.map_snd, ← Category.assoc]
  rw [h_eq]
  have : IsClosedImmersion (Limits.prod.map g (𝟙 Z)) :=
    isClosedImmersion_prod_map_id_right g
  exact IsClosedImmersion.comp _ _

/-- A scheme `X` is projective if it admits a closed immersion into
some `Proj 𝒜` of a graded ring (Lec 7, Prop 8 setting). -/
class Scheme.IsProjective (X : Scheme) : Prop where
  exists_closedImmersion_into_proj :
    ∃ (A : Type) (σ : Type) (_ : CommRing A) (_ : SetLike σ A)
      (_ : AddSubgroupClass σ A) (𝒜 : ℕ → σ) (_ : GradedRing 𝒜)
      (f : X ⟶ Proj 𝒜), IsClosedImmersion f

/-- `Proj 𝒜` is projective via the identity closed immersion. -/
noncomputable instance proj_isProjective
    {A : Type} {σ : Type} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] :
    Scheme.IsProjective (Proj 𝒜) where
  exists_closedImmersion_into_proj :=
    ⟨A, σ, inferInstance, inferInstance, inferInstance, 𝒜, inferInstance,
     𝟙 (Proj 𝒜), inferInstance⟩

/-- The Segre algebra homomorphism sending `X_{(i,j)} ↦ X_i ⊗ X_j`,
underlying the Segre embedding for Lec 7, Prop 8. -/
noncomputable def segreAlgHom (R : Type*) [CommRing R] (n m : ℕ) :
    MvPolynomial (Fin n × Fin m) R →ₐ[R]
    MvPolynomial (Fin n) R ⊗[R] MvPolynomial (Fin m) R :=
  MvPolynomial.aeval (fun p =>
    MvPolynomial.X p.1 ⊗ₜ[R] MvPolynomial.X p.2)

/-- The graph morphism `Γ_f : X ⟶ X × Y` of `f : X ⟶ Y`
(Lec 7, Def 18). -/
noncomputable def graphMorphism {X Y : Scheme} (f : X ⟶ Y) : X ⟶ X ⨯ Y :=
  Limits.prod.lift (𝟙 X) f
