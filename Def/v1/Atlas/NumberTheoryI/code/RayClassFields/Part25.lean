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
import Instance.v1.Atlas.NumberTheoryI.code.RayClassFields.Part10


noncomputable section

open scoped NumberField

namespace RayClassField

variable {K : Type*} [Field K] [NumberField K]

universe u

attribute [instance] instFintypeSignsTimesUnits

noncomputable def instFintypeRayClassGroup (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) : Fintype (RayClassGroup K 𝔪) :=


  @Group.fintypeOfDomOfCoker (QuotientUnits K 𝔪) (RayClassGroup K 𝔪) _ _
    (instFintypeQuotientUnits K 𝔪) (exactSeq_map3 𝔪)
    (Subgroup.normal_of_comm _)
    (Fintype.ofEquiv (ClassGroup (NumberField.RingOfIntegers K))
      ((QuotientGroup.quotientKerEquivOfSurjective
        (exactSeq_map4 𝔪) (exactSeq_surjective 𝔪)).toEquiv.symm.trans
        (Subgroup.quotientEquivOfEq (exactSeq_exact_at_ray_class 𝔪).symm)))

end RayClassField
end
