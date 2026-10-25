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
import Def.v1.Atlas.NumberTheoryI.code.Ch22NormGroup


noncomputable section

open scoped NumberField

open Classical

namespace RayClassField

universe u

lemma fiber_under_finite (K : Type u) (L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Set.Finite {𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L) |
      IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers K) 𝔮 = 𝔭} := by
  have h_inj : Function.Injective
      (fun 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L) => 𝔮.asIdeal) :=
    fun _ _ h => IsDedekindDomain.HeightOneSpectrum.ext h
  apply Set.Finite.subset
  show Set.Finite
    ((fun 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L) => 𝔮.asIdeal) ⁻¹'
      (Ideal.primesOver 𝔭.asIdeal (NumberField.RingOfIntegers L)))
  · exact Set.Finite.preimage
      (Set.InjOn.mono (Set.subset_univ _) (Set.injOn_of_injective h_inj))
      (primesOver_finite _ _)
  · intro 𝔮 h𝔮
    simp only [Set.mem_setOf_eq] at h𝔮
    simp only [Set.mem_preimage, Ideal.primesOver, Set.mem_setOf_eq]
    exact ⟨𝔮.isPrime,
      ⟨by rw [← h𝔮]; simp [IsDedekindDomain.HeightOneSpectrum.under]⟩⟩

theorem extendModulus_finite_support (K : Type u) (L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (𝔪 : Modulus K) :
    Set.Finite {v : Place L | (match v with
      | Place.finite 𝔮 => ramificationIndex' K L 𝔮 * 𝔪.toFun (Place.finite (lyingUnder K L 𝔮))
      | Place.infinite w => if w.IsComplex then 0
          else 𝔪.toFun (Place.infinite (w.comap (algebraMap K L)))) ≠ 0} := by


  apply Set.Finite.subset
  show Set.Finite
    (Set.range Place.infinite ∪
      Place.finite '' {𝔮 | 𝔪.toFun (Place.finite (lyingUnder K L 𝔮)) ≠ 0})
  · apply Set.Finite.union
    · exact Set.finite_range _
    · apply Set.Finite.image


      have h_support : Set.Finite {𝔭 : IsDedekindDomain.HeightOneSpectrum
          (NumberField.RingOfIntegers K) | 𝔪.toFun (Place.finite 𝔭) ≠ 0} := by
        have : {𝔭 | 𝔪.toFun (Place.finite 𝔭) ≠ 0} = Place.finite ⁻¹' {v | 𝔪.toFun v ≠ 0} := rfl
        rw [this]
        exact Set.Finite.preimage
          (fun _ _ _ _ h => Place.finite.inj h) 𝔪.finite_support
      have h_eq : {𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L) |
          𝔪.toFun (Place.finite (lyingUnder K L 𝔮)) ≠ 0} =
        ⋃ 𝔭 ∈ {𝔭 | 𝔪.toFun (Place.finite 𝔭) ≠ 0},
          {𝔮 | IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers K) 𝔮 = 𝔭} := by
        ext 𝔮
        simp only [Set.mem_setOf_eq, Set.mem_iUnion]
        constructor
        · intro h
          exact ⟨lyingUnder K L 𝔮, h, rfl⟩
        · rintro ⟨𝔭, h𝔭, h_eq⟩
          rw [lyingUnder, h_eq]
          exact h𝔭
      rw [h_eq]
      exact h_support.biUnion (fun 𝔭 _ => fiber_under_finite K L 𝔭)
  · intro v hv
    simp only [Set.mem_setOf_eq] at hv
    simp only [Set.mem_union, Set.mem_range, Set.mem_image, Set.mem_setOf_eq]
    cases v with
    | infinite w => left; exact ⟨w, rfl⟩
    | finite 𝔮 =>
      right
      refine ⟨𝔮, ?_, rfl⟩
      intro h_zero
      apply hv
      simp only [h_zero, mul_zero]

end RayClassField
end
