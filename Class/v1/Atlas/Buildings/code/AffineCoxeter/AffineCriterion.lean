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
import Def.v1.Atlas.Buildings.code.AffineCoxeter.AffineCriterion
set_option maxHeartbeats 800000

set_option linter.unusedSectionVars false

open Finset BigOperators CoxeterGroup TitsCone

variable {B : Type*} [DecidableEq B] [Fintype B]


/-- Typeclass packaging the **convexity** of the Tits cone $\mathcal U$. Used locally to allow
the affine criterion to be stated abstractly. -/
class TitsConeConvexity {B : Type*} [DecidableEq B] [Fintype B]
    (M : CoxeterMatrix B) : Prop where
  convex : ∀ (x y : B → ℝ), x ∈ titsConeSet M → y ∈ titsConeSet M →
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    (fun s => (1 - t) * x s + t * y s) ∈ titsConeSet M

