/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteHardField.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
open Filter
open scoped BigOperators Topology


namespace StatMech

namespace Exact3D

noncomputable def finiteFactorNumerator {α : Type*} (s : Finset α)
    (base obs : α → ℝ) (factor : ℝ → α → ℝ) (H : ℝ) : ℝ :=
  ∑ a ∈ s, base a * factor H a * obs a


noncomputable def finiteFactorDenominator {α : Type*} (s : Finset α)
    (base : α → ℝ) (factor : ℝ → α → ℝ) (H : ℝ) : ℝ :=
  ∑ a ∈ s, base a * factor H a


noncomputable def finiteFactorLimitNumerator {α : Type*} (s : Finset α)
    (base obs limitFactor : α → ℝ) : ℝ :=
  ∑ a ∈ s, base a * limitFactor a * obs a


noncomputable def finiteFactorLimitDenominator {α : Type*} (s : Finset α)
    (base limitFactor : α → ℝ) : ℝ :=
  ∑ a ∈ s, base a * limitFactor a


noncomputable def finiteFactorRatio {α : Type*} (s : Finset α)
    (base obs : α → ℝ) (factor : ℝ → α → ℝ) (H : ℝ) : ℝ :=
  finiteFactorNumerator s base obs factor H /
    finiteFactorDenominator s base factor H


noncomputable def finiteFactorLimitRatio {α : Type*} (s : Finset α)
    (base obs limitFactor : α → ℝ) : ℝ :=
  finiteFactorLimitNumerator s base obs limitFactor /
    finiteFactorLimitDenominator s base limitFactor


end Exact3D
end StatMech
