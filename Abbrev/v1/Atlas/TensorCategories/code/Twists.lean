/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Twists.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Abbrev.v1.Atlas.TensorCategories.code.QuasiTensorFunctor.Part5
import Lemma.Category.Atlas.v1.TensorCategories.code.QuasiTensorFunctor
import Lemma.Category.Atlas.v1.TensorCategories.code.MonoidalFunctorsCohomology
import Abbrev.v1.Atlas.TensorCategories.code.QuasiBialgebra
import Def.v1.Atlas.TensorCategories.code.MonoidalFunctorsCohomology.Part5
import Def.v1.Atlas.TensorCategories.code.Twists.Part3
open scoped TensorProduct
open CategoryTheory TensorCategories

universe u


section Def_1_34_6

open scoped TensorProduct

universe v₁

variable (R : Type u) [CommSemiring R]

variable (H : Type v₁) [Semiring H] [Algebra R H]

variable [qb : QuasiBialgebra R H]

/-- Alias for Definition 1.34.6: a twist of a quasi-bialgebra. -/
abbrev Definition_1_34_6_QuasiBialgebraTwist := QuasiBialgebraTwist R H

/-- Alias for Definition 1.34.6: the twisted comultiplication associated to a
quasi-bialgebra twist. -/
noncomputable abbrev Definition_1_34_6_twistedComul
    (tw : QuasiBialgebraTwist R H) (x : H) : H ⊗[R] H :=
  tw.twistedComul x

/-- Alias for Definition 1.34.6: the twisted associator associated to a quasi-bialgebra
twist. -/
noncomputable abbrev Definition_1_34_6_twistedAssociator
    (tw : QuasiBialgebraTwist R H) : H ⊗[R] (H ⊗[R] H) :=
  tw.twistedAssociator

/-- New quasi-bialgebra structure on `H` obtained by twisting an existing one along a
twist `tw`. -/

end Def_1_34_6


section Def_1_34_2

/-- Alias for Definition 1.34.2: twist-equivalence of quasi-fiber functors. -/
abbrev Definition_1_34_2_TwistEquivalent := @QuasiFiberFunctor.TwistEquivalent

end Def_1_34_2
