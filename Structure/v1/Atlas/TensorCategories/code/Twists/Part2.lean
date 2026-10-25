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
import Def.v1.Atlas.TensorCategories.code.Twists.Part4
open scoped TensorProduct
open CategoryTheory TensorCategories

universe u


section TwistMonoidalEquiv

open CategoryTheory

/-- Bundled monoidal equivalence between monoidal categories taking instance
parameters explicitly: an equivalence whose functors in both directions are
monoidal and whose adjunction unit/counit are monoidal natural transformations. -/
structure MonoidalEquiv
    (C : Type*) (D : Type*)
    (instCatC : Category C) (instMonC : @MonoidalCategory C instCatC)
    (instCatD : Category D) (instMonD : @MonoidalCategory D instCatD) where
  equiv : @Equivalence C D instCatC instCatD
  functorMonoidal : @Functor.Monoidal C instCatC instMonC D instCatD instMonD equiv.functor
  inverseMonoidal : @Functor.Monoidal D instCatD instMonD C instCatC instMonC equiv.inverse
  isMonoidal : @Equivalence.IsMonoidal C instCatC instMonC D instCatD instMonD
    equiv functorMonoidal inverseMonoidal

end TwistMonoidalEquiv
