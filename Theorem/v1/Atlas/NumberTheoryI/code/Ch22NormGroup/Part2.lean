/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Ch22NormGroup.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.NumberTheoryI.code.RayClassFields.Part28
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.RayClassFields
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.ValuationBijection
import Theorem.v1.Atlas.NumberTheoryI.code.ValuationBijection
import Def.v1.Atlas.NumberTheoryI.code.Ch22NormGroup.Part2


noncomputable section

open scoped NumberField

open Classical

namespace RayClassField

universe u

lemma cgwz_rearrange {α : Type*} [CommGroupWithZero α] {a b c d e f : α}
    (ha : a ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (h : a * b * c = d * e * f) : f * a⁻¹ = b * d⁻¹ * (c * e⁻¹) := by
  simp only [← div_eq_mul_inv]
  rw [div_mul_div_comm, div_eq_div_iff ha (mul_ne_zero hd he)]
  rw [show f * (d * e) = d * e * f from mul_comm f (d * e)]
  rw [show b * c * a = a * b * c from by rw [mul_comm (b * c), mul_assoc]]
  exact h.symm

lemma algMap_intNorm_den_ne_zero (K : Type u) (L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) :
    (algebraMap (𝓞 K) K) ((Algebra.intNorm (𝓞 K) (𝓞 L)) ↑I.den) ≠ 0 :=
  (map_ne_zero_iff (algebraMap (𝓞 K) K)
    (FaithfulSMul.algebraMap_injective (𝓞 K) K)).mpr
    ((Algebra.intNorm_ne_zero (A := 𝓞 K) (B := 𝓞 L)).mpr
      (nonZeroDivisors.ne_zero I.den.property))

lemma spanSingleton_intNorm_ne_zero (K : Type u) (L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) :
    FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K))
      ((algebraMap (𝓞 K) K) ((Algebra.intNorm (𝓞 K) (𝓞 L)) ↑I.den)) ≠ 0 :=
  FractionalIdeal.spanSingleton_ne_zero_iff.mpr (algMap_intNorm_den_ne_zero K L I)

end RayClassField
end
