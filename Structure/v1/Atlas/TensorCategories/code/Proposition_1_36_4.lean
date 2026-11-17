/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Proposition_1_36_4.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Abbrev.v1.Atlas.TensorCategories.code.QuasiTensorFunctor.Part5
public import Theorem.Category.Atlas.v1.TensorCategories.code.QuasiTensorFunctor
public import Abbrev.v1.Atlas.TensorCategories.code.QuasiBialgebra
public import Def.v1.Atlas.TensorCategories.code.Proposition_1_36_4
public section

open scoped TensorProduct
open CategoryTheory

universe u


/-- A bialgebra twist (Definition 1.36.1): an invertible element `J ∈ H ⊗ H` satisfying
the normalization conditions and the twist (cocycle) equation. -/
structure Prop1364.BialgebraTwist (R : Type u) [CommSemiring R]
    (H : Type u) [Semiring H] [Bialgebra R H] where
  J : (H ⊗[R] H)ˣ
  left_norm : Prop1364.counitTensorId R H J.val = 1
  right_norm : Prop1364.idTensorCounit R H J.val = 1
  cocycle :
    Prop1364.idTensorComul R H J.val * Prop1364.embedRight R H J.val
    = Prop1364.comulTensorId R H J.val * Prop1364.embedLeft R H J.val


