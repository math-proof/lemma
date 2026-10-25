/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/osd_twostagedecay.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.IntegrationSubcriticalAssembly
import Theorem.StatisticalMechanics.Code.OSSS.SharpnessFK
import Theorem.StatisticalMechanics.Code.OSSS.Integration.Part2
open scoped BigOperators
open Real Filter Topology Set Finset

set_option linter.style.longLine false
set_option linter.unusedVariables false


namespace StatMech

namespace Walls

open StatMech.OSSS.IntegrationSubcritical


noncomputable def osd_Sigma (f : ℕ → ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, f k x


end Walls
end StatMech
