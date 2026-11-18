/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TannakaReconstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Tannaka
@[expose] public noncomputable section
set_option maxHeartbeats 800000

open CategoryTheory

universe u


/-- The endomorphism ring of the additive forgetful functor `ModuleCat R ⥤ AddCommGrpCat`,
which by Tannaka reconstruction is canonically isomorphic to `R`. -/
abbrev EndForget₂ (R : Type u) [Ring R] :=
  End (AdditiveFunctor.of (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}))

end
