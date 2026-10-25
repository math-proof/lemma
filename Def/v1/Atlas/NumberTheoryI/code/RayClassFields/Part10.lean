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
import Abbrev.v1.Atlas.NumberTheoryI.code.RayClassFields.Part2


noncomputable section

open scoped NumberField

namespace RayClassField

variable {K : Type*} [Field K] [NumberField K]

universe u

noncomputable def freeGroupToCoprime (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) :
    FreeGroup (CoprimePrimes K 𝔪) →* FracIdealsCoprime K 𝔪 :=
  FreeGroup.lift (fun p => primeCoprime K 𝔪 p.1 p.2)

noncomputable def freeGroupToGal (K : Type u) (L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [IsGalois K L]
    (𝔪 : Modulus K) :
    FreeGroup (CoprimePrimes K 𝔪) →* (L ≃ₐ[K] L) :=
  FreeGroup.lift (fun p => FrobeniusAutomorphism K L p.1)

end RayClassField
end
