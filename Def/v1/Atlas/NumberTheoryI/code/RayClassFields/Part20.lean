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
import Theorem.v1.Atlas.NumberTheoryI.code.RayClassFields.Part11


noncomputable section

open scoped NumberField

namespace RayClassField

variable {K : Type*} [Field K] [NumberField K]

universe u

attribute [instance] instFintypeSignsTimesUnits

def exactSeq_map3 (𝔪 : @Modulus K _ _) :
    QuotientUnits K 𝔪 →* RayClassGroup K 𝔪 :=
  QuotientGroup.lift (UnitsCongruent_in_UnitsCoprime K 𝔪)
    ((QuotientGroup.mk' (RayGroup K 𝔪)).comp (principalIdealMap 𝔪))
    (fun α hα => by
      simp only [MonoidHom.mem_ker]
      exact (QuotientGroup.eq_one_iff _).mpr
        (principalIdealMap_congruent_to_ray 𝔪 α
          (Subgroup.mem_subgroupOf.mp hα)))

noncomputable def exactSeq_map4 (𝔪 : @Modulus K _ _) :
    RayClassGroup K 𝔪 →* ClassGroup (NumberField.RingOfIntegers K) :=
  QuotientGroup.lift (RayGroup K 𝔪)
    (ClassGroup.mk.comp (FracIdealsCoprime_subgroup K 𝔪).subtype)
    (by


      rw [RayGroup, Subgroup.closure_le]
      intro I hI
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply]
      rw [ClassGroup.mk_eq_one_iff, FractionalIdeal.isPrincipal_iff]
      obtain ⟨α, hα_eq, _, _⟩ := hI
      exact ⟨α, by exact_mod_cast hα_eq⟩)

end RayClassField
end
