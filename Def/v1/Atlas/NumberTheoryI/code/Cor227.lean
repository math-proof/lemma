/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor227.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.NumberTheoryI.code.Prop226
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Prop226
import Theorem.v1.Atlas.NumberTheoryI.code.Cor227


noncomputable section

open scoped NumberField

namespace RayClassField

universe u

variable {K : Type u} [Field K] [NumberField K]

noncomputable def Modulus.weight (𝔪 : Modulus K) : ℕ :=
  𝔪.finite_support.toFinset.sum 𝔪.toFun

end RayClassField
end
