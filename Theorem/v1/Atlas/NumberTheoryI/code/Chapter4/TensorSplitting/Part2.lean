/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter4/TensorSplitting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.NumberTheoryI.code.Chapter4.TensorSplitting
open Polynomial TensorProduct


noncomputable section

namespace TensorSplitting

lemma polyEquivTensor'_symm_comp_includeRight
    {K K' : Type*} [Field K] [Field K'] [Algebra K K'] :
    ((polyEquivTensor' K K').symm : K' ⊗[K] Polynomial K →+* Polynomial K').comp
      (↑(Algebra.TensorProduct.includeRight (R := K) (A := K') (B := Polynomial K))
        : Polynomial K →+* K' ⊗[K] Polynomial K) =
      Polynomial.mapRingHom (algebraMap K K') := by
  ext
  case h₁ k =>
    simp only [RingHom.comp_apply, RingHom.coe_coe,
      Algebra.TensorProduct.includeRight_apply, coe_polyEquivTensor'_symm,
      polyEquivTensor_symm_apply_tmul_eq_smul, one_smul, map_C, Polynomial.map_C]
    simp [Polynomial.mapRingHom]
  case h₂ =>
    simp only [RingHom.comp_apply, RingHom.coe_coe,
      Algebra.TensorProduct.includeRight_apply, coe_polyEquivTensor'_symm,
      polyEquivTensor_symm_apply_tmul_eq_smul, one_smul, map_X, Polynomial.map_X]
    simp [Polynomial.mapRingHom]

end TensorSplitting
end
