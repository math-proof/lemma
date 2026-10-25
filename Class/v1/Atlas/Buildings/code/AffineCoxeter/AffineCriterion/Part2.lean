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
import Instance.v1.Atlas.Buildings.code.AffineCoxeter.AffineCriterion
set_option maxHeartbeats 800000

set_option linter.unusedSectionVars false

open Finset BigOperators CoxeterGroup TitsCone

variable {B : Type*} [DecidableEq B] [Fintype B]


/-- Typeclass packaging the **chamber-chasing / orbit-density** property: every point of the
affine hyperplane $E$ lies on a segment between two points of the Tits cone. -/
class ChamberChasingProperty {B : Type*} [DecidableEq B] [Fintype B]
    (M : CoxeterMatrix B) : Prop where
  orbit_density :
    ∀ (v₀ : B → ℝ),
    (∀ s, v₀ s > 0) →
    (∀ t : B, ∑ u : B, v₀ u * formVal M u t = 0) →
    IsAffineCoxeter M →
    ∀ (x : B → ℝ), x ∈ affineHyperplane M v₀ →
    ∃ (p₁ p₂ : B → ℝ) (t : ℝ),
      p₁ ∈ titsConeSet M ∧ p₂ ∈ titsConeSet M ∧
      0 ≤ t ∧ t ≤ 1 ∧
      (∀ s, x s = (1 - t) * p₁ s + t * p₂ s)

