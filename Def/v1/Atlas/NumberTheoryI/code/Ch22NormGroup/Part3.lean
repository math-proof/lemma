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
import Theorem.v1.Atlas.NumberTheoryI.code.Ch22NormGroup.Part2


noncomputable section

open scoped NumberField

open Classical

namespace RayClassField

universe u

def fracRelNorm (K : Type u) (L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] :
    FractionalIdeal (nonZeroDivisors (𝓞 L)) L →*
      FractionalIdeal (nonZeroDivisors (𝓞 K)) K where
  toFun I :=
    ↑(Ideal.relNorm (𝓞 K) I.num) *
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K))
        ((algebraMap (𝓞 K) K) (Algebra.intNorm (𝓞 K) (𝓞 L) I.den))⁻¹
  map_one' := by
    have h1 := FractionalIdeal.den_mul_self_eq_num' (nonZeroDivisors (𝓞 L)) L
      (1 : FractionalIdeal (nonZeroDivisors (𝓞 L)) L)
    rw [mul_one] at h1
    have hnum : (1 : FractionalIdeal (nonZeroDivisors (𝓞 L)) L).num =
        Ideal.span {(↑(1 : FractionalIdeal (nonZeroDivisors (𝓞 L)) L).den : 𝓞 L)} := by
      apply FractionalIdeal.coeIdeal_injective (K := L)
      simp only [FractionalIdeal.coeIdeal_span_singleton]
      exact h1.symm
    rw [hnum, Ideal.relNorm_singleton, FractionalIdeal.coeIdeal_span_singleton,
        FractionalIdeal.spanSingleton_mul_spanSingleton,
        mul_inv_cancel₀ (algMap_intNorm_den_ne_zero K L 1),
        FractionalIdeal.spanSingleton_one]
  map_mul' I J := by
    show ↑((Ideal.relNorm (𝓞 K)) (I * J).num) *
        FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K))
          ((algebraMap (𝓞 K) K) ((Algebra.intNorm (𝓞 K) (𝓞 L)) ↑(I * J).den))⁻¹ =
      (↑((Ideal.relNorm (𝓞 K)) I.num) *
        FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K))
          ((algebraMap (𝓞 K) K) ((Algebra.intNorm (𝓞 K) (𝓞 L)) ↑I.den))⁻¹) *
      (↑((Ideal.relNorm (𝓞 K)) J.num) *
        FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K))
          ((algebraMap (𝓞 K) K) ((Algebra.intNorm (𝓞 K) (𝓞 L)) ↑J.den))⁻¹)
    have hfrac :
        FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K))
            ((algebraMap (𝓞 K) K) ((Algebra.intNorm (𝓞 K) (𝓞 L)) ↑(I * J).den)) *
          ↑((Ideal.relNorm (𝓞 K)) I.num) * ↑((Ideal.relNorm (𝓞 K)) J.num) =
        FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K))
            ((algebraMap (𝓞 K) K) ((Algebra.intNorm (𝓞 K) (𝓞 L)) ↑I.den)) *
          FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K))
            ((algebraMap (𝓞 K) K) ((Algebra.intNorm (𝓞 K) (𝓞 L)) ↑J.den)) *
          ↑((Ideal.relNorm (𝓞 K)) (I * J).num) := by
      have hcross_L : Ideal.span {(↑(I * J).den : 𝓞 L)} * I.num * J.num =
          Ideal.span {(↑I.den : 𝓞 L)} * Ideal.span {(↑J.den : 𝓞 L)} * (I * J).num := by
        apply FractionalIdeal.coeIdeal_injective (K := L)
        push_cast [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton]
        have hI := FractionalIdeal.den_mul_self_eq_num' (nonZeroDivisors (𝓞 L)) L I
        have hJ := FractionalIdeal.den_mul_self_eq_num' (nonZeroDivisors (𝓞 L)) L J
        have hIJ := FractionalIdeal.den_mul_self_eq_num' (nonZeroDivisors (𝓞 L)) L (I * J)
        rw [← hI, ← hJ, ← hIJ]; ring
      have hcross_K := congr_arg (Ideal.relNorm (𝓞 K)) hcross_L
      simp only [map_mul] at hcross_K
      rw [Ideal.relNorm_singleton, Ideal.relNorm_singleton, Ideal.relNorm_singleton] at hcross_K
      have := congr_arg (fun II : Ideal (𝓞 K) =>
        (II : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) hcross_K
      simp only [FractionalIdeal.coeIdeal_mul,
        FractionalIdeal.coeIdeal_span_singleton] at this
      exact this
    rw [← FractionalIdeal.spanSingleton_inv K, ← FractionalIdeal.spanSingleton_inv K,
        ← FractionalIdeal.spanSingleton_inv K]
    exact cgwz_rearrange
      (spanSingleton_intNorm_ne_zero K L (I * J))
      (spanSingleton_intNorm_ne_zero K L I)
      (spanSingleton_intNorm_ne_zero K L J)
      hfrac

noncomputable def fracIdealNorm (K : Type u) (L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [IsGalois K L] :
    (FracIdeal L)ˣ →* (FracIdeal K)ˣ :=
  Units.map (fracRelNorm K L)

end RayClassField
end
