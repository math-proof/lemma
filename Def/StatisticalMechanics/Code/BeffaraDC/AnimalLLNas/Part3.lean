/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLNas.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.KingmanFilling.Part2
import Theorem.StatisticalMechanics.Code.BeffaraDC.AnimalLLNas.Part2
open MeasureTheory Filter Topology Finset
open StatMech.Kingman StatMech.KingmanAE StatMech.KingmanFilling


namespace StatMech

namespace BeffaraDC

variable {ρ : Measure ℝ}


@[nolint unusedArguments]
noncomputable def animalLimit (_ρ : Measure ℝ) : (ℤ → ℝ) → ℝ :=
  kingmanLimit shiftEnv (fun n ω => animalValue ω n)


end BeffaraDC
end StatMech
