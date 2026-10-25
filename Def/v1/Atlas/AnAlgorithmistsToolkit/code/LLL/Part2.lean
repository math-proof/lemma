/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LLL.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Structure.v1.Atlas.AnAlgorithmistsToolkit.code.LLL


noncomputable section

open InnerProductSpace Finset

namespace LLL

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def SatisfiesLovászOriginal (b : Fin n → E) : Prop :=
  ∀ i : Fin n, ∀ hi : (i : ℕ) + 1 < n,
    ‖gramSchmidtVec b i‖ ^ 2 ≤
    4 / 3 * ‖gramSchmidtVec b ⟨i + 1, hi⟩ +
      gramSchmidtCoeff b ⟨i + 1, hi⟩ i • gramSchmidtVec b i‖ ^ 2

end LLL
end
