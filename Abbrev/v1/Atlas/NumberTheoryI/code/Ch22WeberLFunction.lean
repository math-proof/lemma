/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Ch22WeberLFunction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.NumberTheoryI.code.RayClassFields.Part28
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.RayClassFields


noncomputable section

open scoped NumberField

namespace RayClassField

universe u

abbrev RayClassChar (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) : Type u :=
  RayClassGroup K 𝔪 →* ℂˣ

end RayClassField
end
