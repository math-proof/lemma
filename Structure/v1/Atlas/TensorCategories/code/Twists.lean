/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Twists.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Abbrev.v1.Atlas.TensorCategories.code.QuasiTensorFunctor.Part5
public import Theorem.Category.Atlas.v1.TensorCategories.code.QuasiTensorFunctor
public import Lemma.Category.Atlas.v1.TensorCategories.code.MonoidalFunctorsCohomology
public import Abbrev.v1.Atlas.TensorCategories.code.QuasiBialgebra
public import Def.v1.Atlas.TensorCategories.code.MonoidalFunctorsCohomology.Part5
public import Def.v1.Atlas.TensorCategories.code.Twists
public section

open scoped TensorProduct
open CategoryTheory TensorCategories

universe u


section TwistDef

variable (R : Type u) [CommSemiring R]

variable (H : Type u) [Semiring H] [Bialgebra R H]

/-- A bialgebra twist of `H`: a unit `J ∈ (H ⊗ H)ˣ` satisfying the counit
normalization conditions `(ε ⊗ id)(J) = 1`, `(id ⊗ ε)(J) = 1`, and the
cocycle identity. -/
structure BialgebraTwist where
  J : (H ⊗[R] H)ˣ
  left_norm : BialgebraTwist.counitTensorId R H J.val = 1
  right_norm : BialgebraTwist.idTensorCounit R H J.val = 1
  cocycle :
    BialgebraTwist.idTensorComul R H J.val * BialgebraTwist.embedRight R H J.val
    = BialgebraTwist.comulTensorId R H J.val * BialgebraTwist.embedLeft R H J.val

end TwistDef
