/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Ch22NormGroup.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.NumberTheoryI.code.RayClassFields.Part28
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.RayClassFields
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.ValuationBijection
import Theorem.v1.Atlas.NumberTheoryI.code.ValuationBijection
import Def.v1.Atlas.NumberTheoryI.code.Ch22NormGroup.Part4


noncomputable section

open scoped NumberField

open Classical

namespace RayClassField

universe u

lemma rayGroup_le_normGroup (K : Type u) (L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [IsGalois K L]
    (𝔪 : Modulus K) :
    RayGroup K 𝔪 ≤ NormGroup K L 𝔪 :=
  le_sup_left

end RayClassField
end
