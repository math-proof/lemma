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
import Instance.v1.Atlas.NumberTheoryI.code.RayClassFields.Part2


noncomputable section

open scoped NumberField

namespace RayClassField

variable {K : Type*} [Field K] [NumberField K]

universe u

def IsRayGenerator (𝔪 : Modulus K) (I : FracIdealsCoprime K 𝔪) : Prop :=
  ∃ (α : Kˣ),

    (I.val : (FracIdeal K)ˣ).val =
      FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K)) (α : K) ∧

    (∀ v : FinitePlace K, 𝔪 (Place.finite v) ≠ 0 →
      v.valuation K ((α : K) - 1) ≤
        ↑(Multiplicative.ofAdd (-(𝔪 (Place.finite v) : ℤ)))) ∧

    (∀ w : NumberField.InfinitePlace K, 𝔪 (Place.infinite w) ≠ 0 →
      0 < (w.embedding (α : K)).re)

def RayGroup (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) : Subgroup (FracIdealsCoprime K 𝔪) :=
  Subgroup.closure {I | IsRayGenerator 𝔪 I}

def RayClassGroup (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) : Type u :=
  (FracIdealsCoprime K 𝔪) ⧸ (RayGroup K 𝔪)

end RayClassField
end
