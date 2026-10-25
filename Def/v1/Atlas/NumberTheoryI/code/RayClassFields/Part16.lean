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
import Instance.v1.Atlas.NumberTheoryI.code.RayClassFields.Part9


noncomputable section

open scoped NumberField

namespace RayClassField

variable {K : Type*} [Field K] [NumberField K]

universe u

noncomputable def instFintypeSignsTimesUnits (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) : Fintype (SignsTimesUnits K 𝔪) := by
  classical
  unfold SignsTimesUnits
  have hne : 𝔪.finitePartIdeal ≠ ⊥ := by
    unfold Modulus.finitePartIdeal
    rw [ne_eq, ← Ideal.zero_eq_bot, ← ne_eq]
    exact Finset.prod_ne_zero_iff.mpr (fun 𝔭 _ => by
      rw [ne_eq, Ideal.zero_eq_bot, ← ne_eq, ← Ideal.zero_eq_bot]
      exact pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact 𝔭.ne_bot))
  haveI : Finite (NumberField.RingOfIntegers K ⧸ 𝔪.finitePartIdeal) :=
    Ring.HasFiniteQuotients.finiteQuotient hne
  haveI : Fintype (NumberField.RingOfIntegers K ⧸ 𝔪.finitePartIdeal) := Fintype.ofFinite _
  exact inferInstance

end RayClassField
end
