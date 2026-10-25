/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeConvexity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.AffineCoxeter.TitsCone.Part3
import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.WordSigmaInvariance
import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.PosOfAscentProof
import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Set.Finite.List
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open Finset BigOperators CoxeterGroup TitsCone


namespace TitsCone

variable {B : Type*} [DecidableEq B] [Fintype B]

/-- The iterated dual-sigma word action: applying $\sigma_{s_1}^* \sigma_{s_2}^* \cdots$
in left-to-right order. This is the "co-action" version of the reflection action. -/
noncomputable def wordAction (M : CoxeterMatrix B) (ws : List B) (y : B → ℝ) : B → ℝ :=
  ws.foldl (fun v s => dualSigma M s v) y

end TitsCone
