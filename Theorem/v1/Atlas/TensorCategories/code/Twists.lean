/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Twists.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Abbrev.v1.Atlas.TensorCategories.code.QuasiTensorFunctor.Part5
import Lemma.Category.Atlas.v1.TensorCategories.code.QuasiTensorFunctor
import Lemma.Category.Atlas.v1.TensorCategories.code.MonoidalFunctorsCohomology
import Abbrev.v1.Atlas.TensorCategories.code.QuasiBialgebra
import Def.v1.Atlas.TensorCategories.code.MonoidalFunctorsCohomology.Part5
import Def.v1.Atlas.TensorCategories.code.Twists.Part2
open scoped TensorProduct
open CategoryTheory TensorCategories

universe u


section GaugeEquiv

variable {R : Type u} [CommSemiring R]

variable {H : Type u} [Semiring H] [Bialgebra R H]

/-- Reflexivity of gauge equivalence of twists, witnessed by `v = 1`. -/
theorem GaugeEquiv.refl (J : (H ⊗[R] H)ˣ) : GaugeEquiv J J := by
  refine ⟨1, ?_⟩
  simp [Units.val_one, map_one, one_mul, inv_one, ← Algebra.TensorProduct.one_def, mul_one]

/-- Symmetry of gauge equivalence: inverting the witnessing unit `v`. -/
theorem GaugeEquiv.symm {J₁ J₂ : (H ⊗[R] H)ˣ} (h : GaugeEquiv J₁ J₂) :
    GaugeEquiv J₂ J₁ := by
  obtain ⟨v, hv⟩ := h
  refine ⟨v⁻¹, ?_⟩
  simp only [inv_inv]
  rw [hv]
  have hΔ : (Bialgebra.comulAlgHom R H) ↑v⁻¹ * (Bialgebra.comulAlgHom R H) ↑v = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have htmul : ((↑v⁻¹ : H) ⊗ₜ[R] (↑v⁻¹ : H)) * ((↑v : H) ⊗ₜ[R] (↑v : H)) = 1 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul]
    simp [Units.inv_mul, Algebra.TensorProduct.one_def]
  rw [mul_assoc, mul_assoc, mul_assoc, htmul, mul_one]
  rw [← mul_assoc ((Bialgebra.comulAlgHom R H) ↑v⁻¹), hΔ, one_mul]

/-- Transitivity of gauge equivalence: composing the witnessing units. -/
theorem GaugeEquiv.trans {J₁ J₂ J₃ : (H ⊗[R] H)ˣ}
    (h₁₂ : GaugeEquiv J₁ J₂) (h₂₃ : GaugeEquiv J₂ J₃) :
    GaugeEquiv J₁ J₃ := by
  obtain ⟨v₁, hv₁⟩ := h₁₂
  obtain ⟨v₂, hv₂⟩ := h₂₃
  refine ⟨v₂ * v₁, ?_⟩
  rw [hv₂, hv₁]
  simp only [Units.val_mul, map_mul, mul_inv_rev]
  rw [← Algebra.TensorProduct.tmul_mul_tmul]
  simp only [mul_assoc]

end GaugeEquiv
