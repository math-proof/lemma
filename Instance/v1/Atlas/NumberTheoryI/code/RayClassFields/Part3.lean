/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.NumberTheoryI.code.KroneckerWeber.Part5
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.KroneckerWeber
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.IdealFactorization
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.FinitePlaceAbsValue
import Theorem.v1.Atlas.NumberTheoryI.code.IdealFactorization.Part3
import Theorem.v1.Atlas.NumberTheoryI.code.FinitePlaceAbsValue
import Def.v1.Atlas.NumberTheoryI.code.RayClassFields.Part6


noncomputable section

open scoped NumberField

namespace RayClassField

variable {K : Type*} [Field K] [NumberField K]

universe u

instance (𝔪 : @Modulus K _ _) : CommGroup (RayClassGroup K 𝔪) :=
  QuotientGroup.Quotient.commGroup _

end RayClassField
end
