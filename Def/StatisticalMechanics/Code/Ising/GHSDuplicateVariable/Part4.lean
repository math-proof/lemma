/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSDuplicateVariable.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.GHSFull.Part3
import Theorem.StatisticalMechanics.Code.Ising.AizenmanBarsky.Part5
import Theorem.StatisticalMechanics.Code.Ising.GHSThreePoint
import Theorem.StatisticalMechanics.Code.Ising.GHSDuplicateVariable.Part3
open scoped BigOperators symmDiff
open Finset SimpleGraph Set

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000


namespace StatMech

namespace Ising

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def uvar (a b : ConfigSpace V) (w : V) : ℝ := (spin a w - spin b w) / 2


noncomputable def tvar (a b : ConfigSpace V) (w : V) : ℝ := (spin a w + spin b w) / 2


end Ising
end StatMech
