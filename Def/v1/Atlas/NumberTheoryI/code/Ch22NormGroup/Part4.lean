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
import Theorem.v1.Atlas.NumberTheoryI.code.Ch22NormGroup.Part3


noncomputable section

open scoped NumberField

open Classical

namespace RayClassField

universe u

def idealNormMap (K : Type u) (L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [IsGalois K L]
    (𝔪 : Modulus K) :
    FracIdealsCoprime L (extendModulus K L 𝔪) →* FracIdealsCoprime K 𝔪 where
  toFun I := ⟨fracIdealNorm K L I.val, fracIdealNorm_coprime K L 𝔪 I.val I.property⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (fracIdealNorm K L)
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul (fracIdealNorm K L) x.val y.val

def NormGroup (K : Type u) (L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [IsGalois K L]
    (𝔪 : Modulus K) : Subgroup (FracIdealsCoprime K 𝔪) :=
  RayGroup K 𝔪 ⊔ (idealNormMap K L 𝔪).range

end RayClassField
end
