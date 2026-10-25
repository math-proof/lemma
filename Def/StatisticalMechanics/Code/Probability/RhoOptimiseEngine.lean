/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/RhoOptimiseEngine.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Probability.RhoOptimiseEngine
open scoped BigOperators
open Finset
open Real Filter Topology
open intervalIntegral MeasureTheory

set_option linter.style.longLine false


namespace StatMech.Probability

variable {ι : Type*} [Fintype ι]


noncomputable def roe_lhs (d : ι → ℕ) (c : ι → ℝ) (u : ℝ) : ℝ :=
  ∑ i : ι, (d i : ℝ) * (1 - u) ^ (d i - 1) * c i


noncomputable def roe_W (d : ι → ℕ) (c : ι → ℝ) : ℝ :=
  ∑ i : ι, (d i : ℝ) * c i


noncomputable def roe_V (d : ι → ℕ) (c : ι → ℝ) : ℝ :=
  ∑ i ∈ univ.filter (fun i => d i ≠ 0), c i


end StatMech.Probability
