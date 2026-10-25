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
import Theorem.v1.Atlas.NumberTheoryI.code.Ch22NormGroup


noncomputable section

open scoped NumberField

open Classical

namespace RayClassField

universe u

def extendModulus (K : Type u) (L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (𝔪 : Modulus K) : Modulus L where
  toFun v := match v with
    | Place.finite 𝔮 => ramificationIndex' K L 𝔮 * 𝔪.toFun (Place.finite (lyingUnder K L 𝔮))
    | Place.infinite w => if w.IsComplex then 0
        else 𝔪.toFun (Place.infinite (w.comap (algebraMap K L)))
  finite_support := extendModulus_finite_support K L 𝔪
  inf_le_one := by
    intro w
    simp only
    split_ifs with h
    · exact Nat.zero_le _
    · exact 𝔪.inf_le_one _
  complex_zero := by
    intro w hw
    simp only [hw, ↓reduceIte]

end RayClassField
end
