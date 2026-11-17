/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LLL.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Structure.v1.Atlas.AnAlgorithmistsToolkit.code.LLL

@[expose] public section

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
