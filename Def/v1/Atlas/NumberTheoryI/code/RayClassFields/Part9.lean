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
import Theorem.v1.Atlas.NumberTheoryI.code.RayClassFields.Part3


noncomputable section

open scoped NumberField

namespace RayClassField

variable {K : Type*} [Field K] [NumberField K]

universe u

noncomputable def primeCoprime (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝔭 : FinitePlace K) (h𝔭 : 𝔪 (Place.finite 𝔭) = 0) :
    FracIdealsCoprime K 𝔪 :=
  ⟨primeAsUnitFracIdeal K 𝔭, primeAsUnitFracIdeal_coprime K 𝔪 𝔭 h𝔭⟩

def primesCoprime (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) : Set (FracIdealsCoprime K 𝔪) :=
  {I | ∃ (𝔭 : FinitePlace K) (h𝔭 : 𝔪 (Place.finite 𝔭) = 0), I = primeCoprime K 𝔪 𝔭 h𝔭}

end RayClassField
end
