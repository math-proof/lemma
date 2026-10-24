/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/PerronFrobeniusFin1.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.TensorCategories.code.FrobeniusPerron
import Lemma.Category.Atlas.v1.TensorCategories.code.FrobeniusPerron

open FusionRing

section VerifyFin1Instance

noncomputable example : HasPerronFrobeniusProperty (Fin 1) := inferInstance

noncomputable example (M : Matrix (Fin 1) (Fin 1) ℝ) (hM : ∀ i j, 0 < M i j) :
    PerronFrobenius M :=
  perron_frobenius_pos_matrix M hM

example (M : Matrix (Fin 1) (Fin 1) ℝ) (hM : ∀ i j, 0 < M i j) :
    let pf := HasPerronFrobeniusProperty.pfEigenvec M hM
    pf.1 = M 0 0 ∨ True := by
  left; rfl

end VerifyFin1Instance
