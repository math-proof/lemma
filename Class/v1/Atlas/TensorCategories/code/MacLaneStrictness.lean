/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MacLaneStrictness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.End
import Mathlib.CategoryTheory.Monoidal.Skeleton
import Mathlib.CategoryTheory.Monoidal.Transport
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.CategoryTheory.Monoidal.Free.Coherence
import Mathlib.CategoryTheory.Monoidal.Free.Basic
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category


namespace EGNO.MacLaneStrictness

/-- Definition 1.8.1: A monoidal category is strict if the associator and unitors are
identity morphisms, i.e. `(X ⊗ Y) ⊗ Z = X ⊗ (Y ⊗ Z)`, `𝟙_C ⊗ X = X`, and `X ⊗ 𝟙_C = X`
on the nose, with the structure isomorphisms equal to the corresponding `eqToHom`. -/
class MonoidalCategory.IsStrict (C : Type*) [Category C] [MonoidalCategory C] : Prop where
  tensorObj_assoc : ∀ (X Y Z : C), (X ⊗ Y) ⊗ Z = X ⊗ (Y ⊗ Z)
  tensorUnit_left : ∀ (X : C), 𝟙_ C ⊗ X = X
  tensorUnit_right : ∀ (X : C), X ⊗ 𝟙_ C = X
  associator_eqToHom : ∀ (X Y Z : C),
    (α_ X Y Z).hom = eqToHom (tensorObj_assoc X Y Z)
  leftUnitor_eqToHom : ∀ (X : C),
    (λ_ X).hom = eqToHom (tensorUnit_left X)
  rightUnitor_eqToHom : ∀ (X : C),
    (ρ_ X).hom = eqToHom (tensorUnit_right X)

end EGNO.MacLaneStrictness
