/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MacLaneStrictness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.End
public import Mathlib.CategoryTheory.Monoidal.Skeleton
public import Mathlib.CategoryTheory.Monoidal.Transport
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import Mathlib.CategoryTheory.Monoidal.Free.Coherence
public import Mathlib.CategoryTheory.Monoidal.Free.Basic
public import Abbrev.v1.Atlas.TensorCategories.code.MacLaneStrictness
@[expose] public section

set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category


namespace EGNO.MacLaneStrictness

section StrictnessTheorem

universe v u

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]

attribute [local instance] endofunctorMonoidalCategory

/-- The right-tensoring functor `C → C ⥤ C`, `X ↦ • ⊗ X`, is naturally a monoidal functor,
giving the monoidal embedding of `C` into its category of endofunctors. -/
instance tensoringRight_monoidal : (tensoringRight C).Monoidal := inferInstance

end StrictnessTheorem
end EGNO.MacLaneStrictness
