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

noncomputable section

open InnerProductSpace Finset

namespace LLL

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def gramSchmidtVec (b : Fin n → E) : Fin n → E :=
  gramSchmidt ℝ b

def gramSchmidtCoeff (b : Fin n → E) (i j : Fin n) : ℝ :=
  @inner ℝ E _ (gramSchmidtVec b j) (b i) / (‖gramSchmidtVec b j‖ ^ 2)

def IsSizeReduced (b : Fin n → E) : Prop :=
  ∀ i j : Fin n, j < i → |gramSchmidtCoeff b i j| ≤ 1 / 2

def SatisfiesLovász (b : Fin n → E) : Prop :=
  ∀ i : Fin n, ∀ hi : (i : ℕ) + 1 < n,
    ‖gramSchmidtVec b ⟨i + 1, hi⟩ +
      gramSchmidtCoeff b ⟨i + 1, hi⟩ i • gramSchmidtVec b i‖ ^ 2 ≥
    3 / 4 * ‖gramSchmidtVec b i‖ ^ 2

structure IsLLLReduced (b : Fin n → E) : Prop where
  size_reduced : IsSizeReduced b
  lovász : SatisfiesLovász b


def SatisfiesLovászOriginal (b : Fin n → E) : Prop :=
  ∀ i : Fin n, ∀ hi : (i : ℕ) + 1 < n,
    ‖gramSchmidtVec b i‖ ^ 2 ≤
    4 / 3 * ‖gramSchmidtVec b ⟨i + 1, hi⟩ +
      gramSchmidtCoeff b ⟨i + 1, hi⟩ i • gramSchmidtVec b i‖ ^ 2

structure IsReducedBasis (b : Fin n → E) : Prop where
  size_reduced : IsSizeReduced b
  lovász_original : SatisfiesLovászOriginal b

end LLL

end
