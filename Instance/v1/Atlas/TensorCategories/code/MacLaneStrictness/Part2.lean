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
import Abbrev.v1.Atlas.TensorCategories.code.MacLaneStrictness
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category


namespace EGNO.MacLaneStrictness

section StrictnessTheorem

universe v u

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]

/-- The right-tensoring functor `C → C ⥤ C`, `X ↦ • ⊗ X`, is naturally a monoidal functor,
giving the monoidal embedding of `C` into its category of endofunctors. -/
instance tensoringRight_monoidal : (tensoringRight C).Monoidal := inferInstance

end StrictnessTheorem
end EGNO.MacLaneStrictness
