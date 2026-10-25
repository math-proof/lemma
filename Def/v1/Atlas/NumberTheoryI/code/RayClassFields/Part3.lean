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
import Structure.v1.Atlas.NumberTheoryI.code.RayClassFields.Part2


noncomputable section

open scoped NumberField

namespace RayClassField

variable {K : Type*} [Field K] [NumberField K]

def SimpleModulus.trivial : SimpleModulus K where
  finite_part := ⊤
  infinite_part := ∅
  real_places := by simp

def Modulus.finitePartIdeal (𝔪 : @Modulus K _ _) : Ideal (NumberField.RingOfIntegers K) :=
  let S := 𝔪.finite_support.preimage (f := Place.finite)
    (fun a _ b _ hab => by cases hab; rfl)
  S.toFinset.prod (fun 𝔭 => 𝔭.asIdeal ^ 𝔪 (Place.finite 𝔭))

def Modulus.dvd (𝔪 𝔫 : Modulus K) : Prop :=
  ∀ v, 𝔪 v ≤ 𝔫 v

def Modulus.gcd (𝔪 𝔫 : Modulus K) : Modulus K where
  toFun v := min (𝔪 v) (𝔫 v)
  finite_support := by
    apply Set.Finite.subset (𝔪.finite_support.union 𝔫.finite_support)
    intro v hv
    simp only [Set.mem_setOf_eq, Set.mem_union] at *
    by_contra h
    push Not at h
    exact hv (by simp [h.1, h.2])
  inf_le_one := fun v => le_trans (min_le_left _ _) (𝔪.inf_le_one v)
  complex_zero := fun v hv => by simp [𝔪.complex_zero v hv, 𝔫.complex_zero v hv]

def Modulus.lcm (𝔪 𝔫 : Modulus K) : Modulus K where
  toFun v := max (𝔪 v) (𝔫 v)
  finite_support := by
    apply Set.Finite.subset (𝔪.finite_support.union 𝔫.finite_support)
    intro v hv
    simp only [Set.mem_setOf_eq, Set.mem_union] at *
    by_contra h
    push Not at h
    exact hv (by simp [h.1, h.2])
  inf_le_one := fun v => max_le (𝔪.inf_le_one v) (𝔫.inf_le_one v)
  complex_zero := fun v hv => by simp [𝔪.complex_zero v hv, 𝔫.complex_zero v hv]

def Modulus.trivial : Modulus K where
  toFun _ := 0
  finite_support := by simp
  inf_le_one _ := Nat.zero_le _
  complex_zero _ _ := rfl

end RayClassField
end
