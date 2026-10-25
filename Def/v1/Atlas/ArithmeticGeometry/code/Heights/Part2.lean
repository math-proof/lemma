/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Heights.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.v1.Atlas.ArithmeticGeometry.code.GaloisPlaceHelper
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.GaloisPlaceHelper
import Theorem.v1.Atlas.ArithmeticGeometry.code.Heights


noncomputable section

open Height MvPolynomial

namespace AbsoluteHeight

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Empty.Finite ι]

noncomputable def galoisEquivFinitePlace {K : Type*} [Field K] [NumberField K]
    (σ : K ≃ₐ[ℚ] K) : NumberField.FinitePlace K ≃ NumberField.FinitePlace K where
  toFun v := ⟨v.val.comp (f := (σ.symm : K →+* K)) σ.symm.injective,
    NumberField.FinitePlace.isFinitePlace_comp_galois σ v⟩
  invFun v := ⟨v.val.comp (f := (σ : K →+* K)) σ.injective, by
    have h := NumberField.FinitePlace.isFinitePlace_comp_galois σ⁻¹ v
    simp only [show (σ⁻¹ : K ≃ₐ[ℚ] K) = σ.symm from by ext; rfl,
      AlgEquiv.symm_symm] at h
    exact h⟩
  left_inv v := by
    apply Subtype.ext; apply AbsoluteValue.ext; intro x
    show v (σ.symm (σ x)) = v x
    rw [AlgEquiv.symm_apply_apply]
  right_inv v := by
    apply Subtype.ext; apply AbsoluteValue.ext; intro x
    show v (σ (σ.symm x)) = v x
    rw [AlgEquiv.apply_symm_apply]

end AbsoluteHeight
end
