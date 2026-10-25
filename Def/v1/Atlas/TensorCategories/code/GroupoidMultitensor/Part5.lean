/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GroupoidMultitensor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.GradedObject
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Algebra.Pi
import Structure.v1.Atlas.TensorCategories.code.GroupoidMultitensor.Part4
set_option maxHeartbeats 800000

open CategoryTheory

universe u v w


namespace GroupoidMultitensor

attribute [instance] FiniteGroupoidData.finObj FiniteGroupoidData.finMor

attribute [instance] FiniteGroupoidData.decEqObj FiniteGroupoidData.decEqMor

attribute [instance] GroupoidGradedVecData.instAddCommMonoid GroupoidGradedVecData.instModule

attribute [instance] MatrixVecData.instAddCommMonoid MatrixVecData.instModule

attribute [instance] ProductMatrixGroupVecData.instAddCommMonoid

attribute [instance] ProductMatrixGroupVecData.instModule

/-- Category structure on `ProductMatrixGroupVecData` with componentwise linear maps. -/
@[reducible]
def pmgvCategoryInstance (k : Type w) [Field k]
    {m : ℕ} (n : Fin m → ℕ)
    (G : (i : Fin m) → Type w)
    [∀ i, Group (G i)] [∀ i, Fintype (G i)] [∀ i, DecidableEq (G i)] :
    Category.{w} (ProductMatrixGroupVecData k n G) where
  Hom V W := ∀ (i : Fin m) (j₁ j₂ : Fin (n i)) (g : G i),
    V.component i j₁ j₂ g →ₗ[k] W.component i j₁ j₂ g
  id V i j₁ j₂ g := LinearMap.id
  comp f h i j₁ j₂ g := (h i j₁ j₂ g).comp (f i j₁ j₂ g)
  id_comp f := by funext i j₁ j₂ g; simp [LinearMap.comp_id]
  comp_id f := by funext i j₁ j₂ g; simp [LinearMap.id_comp]
  assoc f g h := by funext i j₁ j₂ gg; rfl

/-- Monoidal structure on `ProductMatrixGroupVecData` combining matrix multiplication and the
group multiplications of the components. -/
def AreMonoidallyEquivalent
    (C : Type*) (catC : Category C) (monC : @MonoidalCategory C catC)
    (D : Type*) (catD : Category D) (monD : @MonoidalCategory D catD) : Prop :=
  ∃ (E : @Equivalence C D catC catD),
    Nonempty (@Functor.LaxMonoidal C catC monC D catD monD E.functor)

/-- The monoidal category of pair-groupoid-graded vector spaces on `X` is monoidally equivalent
to the matrix vector-space category of size `|X|`. -/
def componentSubcategoryGrading (G : FiniteGroupoidData) (x y : G.Obj) :=
  G.MorBetween x y

/-- Bridge from a Mathlib `Groupoid` instance with finite Hom sets to `FiniteGroupoidData`. -/
noncomputable def fromMathlibGroupoid (X : Type u) [Fintype X] [DecidableEq X]
    [CategoryTheory.Groupoid X]
    [∀ (x y : X), Fintype (x ⟶ y)]
    [∀ (x y : X), DecidableEq (x ⟶ y)] :
    FiniteGroupoidData.{u, max u v} where
  Obj := X
  Mor := Σ (p : X × X), (p.1 ⟶ p.2)
  finObj := inferInstance
  finMor := inferInstance
  decEqObj := inferInstance
  decEqMor := inferInstance
  src := fun g => g.1.1
  tgt := fun g => g.1.2
  comp := fun g h p => by
    refine ⟨(g.1.1, h.1.2), ?_⟩
    have : g.1.2 = h.1.1 := p
    exact g.2 ≫ (this ▸ h.2)
  id := fun x => ⟨(x, x), 𝟙 x⟩
  inv := fun g => ⟨(g.1.2, g.1.1), CategoryTheory.Groupoid.inv g.2⟩
  src_id := fun _ => rfl
  tgt_id := fun _ => rfl
  src_comp := fun _ _ _ => rfl
  tgt_comp := fun _ _ _ => rfl
  src_inv := fun _ => rfl
  tgt_inv := fun _ => rfl

end GroupoidMultitensor
