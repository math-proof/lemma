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
import Theorem.v1.Atlas.Buildings.code.AffineCoxeter.TitsConeConvexity.Part2
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open Finset BigOperators CoxeterGroup TitsCone


namespace TitsCone

variable {B : Type*} [DecidableEq B] [Fintype B]

/-- The face $w \cdot F_I = \sigma^*_w(F_I)$: image of the standard face indexed by $I \subseteq S$
under the word action of $w$. -/
def wordFace (M : CoxeterMatrix B) (ws : List B) (I : Finset B) : Set (B → ℝ) :=
  (wordAction M ws) '' (titsFaceDual M I)

end TitsCone
