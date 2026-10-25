/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WeightedDerivExpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Def.v1.Atlas.DifferentialAnalysis.code.DistributionalKernels2
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.DistributionalKernels2
import Instance.v1.Atlas.DifferentialAnalysis.code.WeightedDerivExpansion


noncomputable section

open BigOperators

open scoped SchwartzMap

namespace WeightedDerivExpansion

/-- The total size of the componentwise difference `γ - α` of multi-indices. -/
def multiIndexDiffSize {n : ℕ} (γ α : Fin n → ℕ) : ℕ :=
  ∑ i : Fin n, (γ i - α i)

end WeightedDerivExpansion
end
