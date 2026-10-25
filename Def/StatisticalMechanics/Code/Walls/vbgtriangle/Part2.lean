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
import Theorem.StatisticalMechanics.Code.Walls.vbgtriangle
open scoped BigOperators
open Finset


namespace StatMech

namespace Walls

namespace VBG

set_option linter.unusedSectionVars false

set_option linter.style.longLine false

set_option maxHeartbeats 800000


variable {Ω : Type*} [Fintype Ω]


section Prop1

variable (μ : Ω → ℝ) (X Y Z : Ω → ℝ)


section CondFKG

open StatMech.ConfigSpace

variable {E : Type*} [Fintype E] [DecidableEq E]


noncomputable def vbg_coordUp (j : E) (ω : ConfigSpace E) : ℝ := if ω j then 1 else 0


noncomputable def vbg_coordDown (j : E) (ω : ConfigSpace E) : ℝ := if ω j then 0 else 1


end CondFKG
end Prop1
end VBG
end Walls
end StatMech
