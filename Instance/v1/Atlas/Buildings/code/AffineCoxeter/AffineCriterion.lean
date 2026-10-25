/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/AffineCriterion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.Buildings.code.AffineCoxeter.PerronFrobeniusProof
import Def.v1.Atlas.Buildings.code.AffineCoxeter.TitsConeConvexity.Part3
import Theorem.v1.Atlas.Buildings.code.AffineCoxeter.TitsConeFiniteParabolic.Part4
import Class.v1.Atlas.Buildings.code.AffineCoxeter.AffineCriterion
set_option maxHeartbeats 800000

set_option linter.unusedSectionVars false

open Finset BigOperators CoxeterGroup TitsCone

variable {B : Type*} [DecidableEq B] [Fintype B]


/-- Default instance: convexity of $\mathcal U$ follows from `titsConeSet_convex`. -/
instance titsConeConvexity_instance (M : CoxeterMatrix B) : TitsConeConvexity M where
  convex := by
    intro x y hx hy t ht0 ht1
    have h1t : 0 ≤ 1 - t := by linarith
    have hab : (1 - t) + t = 1 := by ring
    have hconv := titsConeSet_convex M hx hy h1t ht0 hab
    convert hconv using 1

