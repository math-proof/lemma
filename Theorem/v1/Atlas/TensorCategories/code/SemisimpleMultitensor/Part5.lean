/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SemisimpleMultitensor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Structure.v1.Atlas.TensorCategories.code.PivotalSpherical.Part3
import Lemma.Category.Atlas.v1.TensorCategories.code.PivotalSpherical
import Def.v1.Atlas.TensorCategories.code.SemisimpleMultitensor.Part5
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory CategoryTheory.Limits

universe v u


noncomputable section

namespace CategoryTheory

section UnitSemisimple

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasZeroMorphisms C]

section ObjectDecomposition

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [Preadditive C] [MonoidalPreadditive C] [HasFiniteBiproducts C]

/-- Every object `X` decomposes as a biproduct of its `(i, j)`-component objects
`f i ⊗ X ⊗ f j`, where `f` is the chosen decomposition of the unit into simple summands. -/
theorem object_componentDecomposition {n : ℕ} (f : Fin n → C) [HasBiproduct f]
    (hiso : 𝟙_ C ≅ ⨁ f) (hsimp : ∀ i, Simple (f i))
    (X : C) :
    ∃ (_ : HasBiproduct (componentFamily f X)),
      Nonempty (X ≅ ⨁ (componentFamily f X)) := by
  refine ⟨inferInstance, ⟨?_⟩⟩

  have step1 : X ≅ (⨁ f) ⊗ (X ⊗ ⨁ f) :=
    (λ_ X).symm ≪≫ tensorIso (Iso.refl (𝟙_ C)) (ρ_ X).symm ≪≫
    tensorIso hiso (tensorIso (Iso.refl X) hiso)

  have step2 : (⨁ f) ⊗ (X ⊗ ⨁ f) ≅ ⨁ (fun i => f i ⊗ (X ⊗ ⨁ f)) :=
    rightDistributor f (X ⊗ ⨁ f)

  have step3 : (⨁ fun i => f i ⊗ (X ⊗ ⨁ f)) ≅ (⨁ fun i => ⨁ fun j => f i ⊗ (X ⊗ f j)) :=
    biproduct.mapIso fun i =>
      tensorIso (Iso.refl (f i)) (leftDistributor X f) ≪≫
      leftDistributor (f i) (fun j => X ⊗ f j)

  have step4 : (⨁ fun i => ⨁ fun j => f i ⊗ (X ⊗ f j)) ≅ ⨁ componentFamily f X :=
    biproductFlattenIso (fun i j => f i ⊗ (X ⊗ f j))
  exact step1 ≪≫ step2 ≪≫ step3 ≪≫ step4

end ObjectDecomposition
end UnitSemisimple
end CategoryTheory
end
