/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/vbgtriangle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
import Theorem.StatisticalMechanics.Code.Ising.AizenmanBarsky.Part5
import Theorem.StatisticalMechanics.Code.Ising.IsingFKGLayer
import Theorem.StatisticalMechanics.Code.Walls.ghc_urselleqgap
import Theorem.StatisticalMechanics.Code.Walls.vbgtriangle.Part2
open scoped BigOperators
open Finset


namespace StatMech

namespace Walls

namespace VBG

set_option linter.unusedSectionVars false

set_option linter.style.longLine false

set_option maxHeartbeats 800000


variable {Ω : Type*} [Fintype Ω]


section MachineCheck

noncomputable def mcMu : Fin 4 → ℝ := ![0.4, 0.1, 0.3, 0.2]


noncomputable def mcX : Fin 4 → ℝ := ![1, 0, 1, 0]


noncomputable def mcY : Fin 4 → ℝ := ![1, 1, 0, 0]


noncomputable def mcZ : Fin 4 → ℝ := ![0, 1, 1, 0]


end MachineCheck
end VBG
end Walls
end StatMech
