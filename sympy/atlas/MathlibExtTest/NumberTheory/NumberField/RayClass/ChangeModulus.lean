/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/RayClass/ChangeModulus.lean -/

import sympy.atlas.NumberTheory.NumberField.RayClass.ChangeModulus
import Lemma.Nat.NumberField.RayClass.ChangeModulus

open scoped nonZeroDivisors
open NumberField
open NumberField.Modulus

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

-- Helper equality: ambient subgroup of `changeModulus`.
example {m1 m2 : Modulus K} (C1 : CongruenceSubgroup m1) :
    (changeModulus C1 m2).toAmbientSubgroup =
      (C1.toAmbientSubgroup ⊓ coprimeFractionalIdeals m2) ⊔
        rayGroupAmbient m2 :=
  changeModulus_toAmbientSubgroup C1

-- Simplified helper equality under `m2 ∣ m1`.
example {m1 m2 : Modulus K} (C1 : CongruenceSubgroup m1)
    (hdiv : m2 ∣ m1) :
    (changeModulus C1 m2).toAmbientSubgroup =
      C1.toAmbientSubgroup ⊔ rayGroupAmbient m2 :=
  changeModulus_toAmbientSubgroup_of_dvd C1 hdiv

-- Canonical change of modulus is equivalent under the ray condition.
example {m1 m2 : Modulus K} (C1 : CongruenceSubgroup m1)
    (hdiv : m2 ∣ m1)
    (hcond : coprimeFractionalIdeals m1 ⊓ rayGroupAmbient m2 ≤
      C1.toAmbientSubgroup) :
    CongruenceSubgroupPair.IsEquivalent
      { modulus := m1, subgroup := C1 }
      { modulus := m2, subgroup := changeModulus C1 m2 } :=
  changeModulus_isEquivalent C1 hdiv hcond

-- Forward direction of the N422 iff.
example {m1 m2 : Modulus K} (C1 : CongruenceSubgroup m1)
    (hdiv : m2 ∣ m1)
    (h : ∃ C2 : CongruenceSubgroup m2,
      CongruenceSubgroupPair.IsEquivalent
        { modulus := m1, subgroup := C1 }
        { modulus := m2, subgroup := C2 }) :
    coprimeFractionalIdeals m1 ⊓ rayGroupAmbient m2 ≤
      C1.toAmbientSubgroup :=
  (exists_equivalent_iff_changeModulus C1 hdiv).mp h

-- Reverse direction of the N422 iff (witness is `changeModulus`).
example {m1 m2 : Modulus K} (C1 : CongruenceSubgroup m1)
    (hdiv : m2 ∣ m1)
    (h : coprimeFractionalIdeals m1 ⊓ rayGroupAmbient m2 ≤
      C1.toAmbientSubgroup) :
    ∃ C2 : CongruenceSubgroup m2,
      CongruenceSubgroupPair.IsEquivalent
        { modulus := m1, subgroup := C1 }
        { modulus := m2, subgroup := C2 } :=
  (exists_equivalent_iff_changeModulus C1 hdiv).mpr h
