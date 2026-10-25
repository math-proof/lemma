/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GrothendieckFusionRingInstance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.TensorCategories.code.FiniteTensorCategory.Part8
import Lemma.Category.Atlas.v1.TensorCategories.code.FiniteTensorCategory
import Lemma.Category.Atlas.v1.TensorCategories.code.GrothendieckRingCategorical
import Def.v1.Atlas.TensorCategories.code.GrothendieckRingCategorical.Part4
import Def.v1.Atlas.TensorCategories.code.GrothendieckFusionRingInstance
open CategoryTheory MonoidalCategory Finset

universe v u


namespace CategoryTheory

section JHLift

variable {κ : Type*} [Field κ] {C : Type u} [Category.{v} C]
  [Preadditive C] [Linear κ C] [Abelian C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear κ C]
  [RigidCategory C]
  [cfd : CategoricalFusionData κ C]
  [jh : HasJordanHolderMultiplicities κ C]

/-- The lifted Frobenius-Perron dimension of the unit object equals `1`. -/
theorem jhFpDim_unit
    (fpd : (CategoricalFusionData.toFusionRing (κ := κ) (C := C)).FPdimData) :
    jhFpDim fpd (𝟙_ C) = 1 := by
  simp only [jhFpDim, jh.mult_unit]

  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ cfd.unitIdx (fun i => fpd.d i)]
  simp only [Finset.mem_univ, ite_true]
  exact fpd.d_unit

/-- The lifted Frobenius-Perron dimension is strictly positive on every object. -/
theorem jhFpDim_pos
    (fpd : (CategoricalFusionData.toFusionRing (κ := κ) (C := C)).FPdimData)
    (X : C) : jhFpDim fpd X > 0 := by
  simp only [jhFpDim]
  obtain ⟨i₀, hi₀⟩ := jh.mult_nontrivial X
  exact lt_of_lt_of_le
    (mul_pos (Nat.cast_pos.mpr hi₀) (fpd.d_pos i₀))
    (Finset.single_le_sum
      (fun i _ => mul_nonneg (Nat.cast_nonneg _) (le_of_lt (fpd.d_pos i)))
      (Finset.mem_univ i₀))

/-- The lifted Frobenius-Perron dimension is multiplicative on tensor products. -/
theorem jhFpDim_tensor
    (fpd : (CategoricalFusionData.toFusionRing (κ := κ) (C := C)).FPdimData)
    (X Y : C) : jhFpDim fpd (X ⊗ Y) = jhFpDim fpd X * jhFpDim fpd Y := by
  simp only [jhFpDim, jh.mult_tensor X Y]


  rw [Finset.sum_mul]


  have key : ∀ l : cfd.ι,
    (↑(∑ i : cfd.ι, ∑ j : cfd.ι, jh.mult X i * jh.mult Y j * cfd.N i j l) : ℝ) * fpd.d l =
    ∑ i : cfd.ι, ∑ j : cfd.ι, (jh.mult X i : ℝ) * (jh.mult Y j : ℝ) * (cfd.N i j l : ℝ) * fpd.d l := by
    intro l; push_cast; rw [Finset.sum_mul]; congr 1; ext i
    rw [Finset.sum_mul]
  simp_rw [key]; clear key

  conv_rhs =>
    arg 2; ext i
    rw [mul_comm, Finset.sum_mul]
    arg 2; ext j
    rw [show (jh.mult Y j : ℝ) * fpd.d j * ((jh.mult X i : ℝ) * fpd.d i) =
        (jh.mult X i : ℝ) * (jh.mult Y j : ℝ) * (fpd.d i * fpd.d j) by ring]
    rw [fpd.d_mul i j, Finset.mul_sum]


  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
  congr 1; ext i
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
  congr 1; ext j
  congr 1; ext k
  simp [CategoricalFusionData.toFusionRing]; ring

/-- The lifted Frobenius-Perron dimension is invariant under isomorphism. -/
theorem jhFpDim_iso
    (fpd : (CategoricalFusionData.toFusionRing (κ := κ) (C := C)).FPdimData)
    (X Y : C) (h : Nonempty (X ≅ Y)) : jhFpDim fpd X = jhFpDim fpd Y := by
  simp only [jhFpDim]
  congr 1; ext i
  congr 1
  exact_mod_cast jh.mult_iso X Y h i

end JHLift
end CategoryTheory
