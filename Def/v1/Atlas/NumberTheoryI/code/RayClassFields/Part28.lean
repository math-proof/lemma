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
import Structure.v1.Atlas.NumberTheoryI.code.RayClassFields.Part4


noncomputable section

open scoped NumberField

namespace RayClassField

variable {K : Type*} [Field K] [NumberField K]

universe u

attribute [instance] instFintypeSignsTimesUnits

attribute [instance] instFintypeRayClassGroup

def CongruenceSubgroupPair.toAmbientSubgroup {K : Type u} [Field K] [NumberField K]
    (p : CongruenceSubgroupPair K) : Subgroup (FracIdeal K)ˣ :=
  p.subgroup.map (FracIdealsCoprime_subgroup K p.modulus).subtype

def CongruenceSubgroupPair.IsEquiv {K : Type u} [Field K] [NumberField K]
    (p₁ p₂ : CongruenceSubgroupPair K) : Prop :=
  (FracIdealsCoprime_subgroup K p₁.modulus) ⊓ p₂.toAmbientSubgroup =
  (FracIdealsCoprime_subgroup K p₂.modulus) ⊓ p₁.toAmbientSubgroup

def IsHilbertClassField (K : Type u) (L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [KroneckerWeber.IsAbelianExtension K L] : Prop :=
  IsRayClassField K L Modulus.trivial

end RayClassField
end
