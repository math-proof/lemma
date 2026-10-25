/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeFiniteParabolic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.AffineCoxeter.TitsCone.Part3
import Def.v1.Atlas.Buildings.code.AffineCoxeter.TitsConeConvexity.Part3
import Mathlib.Order.Filter.Basic
import Theorem.v1.Atlas.Buildings.code.AffineCoxeter.TitsConeFiniteParabolic.Part2
set_option linter.unusedSectionVars false

open Finset BigOperators CoxeterGroup TitsCone


namespace TitsCone

variable {B : Type*} [DecidableEq B] [Fintype B]

/-- Two abstract finiteness hypotheses that supply the standard $\Phi^+$ with a
`RootSystemData` structure: $(1)$ finiteness of roots supported on a proper subset,
and $(2)$ finiteness of nonposRoots on the radical hyperplane. -/
structure FiniteProperParabolicsHyp (M : CoxeterMatrix B) : Prop where
  finiteRoots_in_subspan_of_subset_finite :
    ∀ (I : Finset B), I ≠ Finset.univ →
      Set.Finite {α ∈ standardΦpos M | ∀ s : B, s ∉ I → α s = 0}
  hyperplane_nonposRoots_finite :
    ∀ (v₀ : B → ℝ),
    (∀ s, v₀ s > 0) →
    (∀ t : B, ∑ u : B, v₀ u * CoxeterGroup.formVal M u t = 0) →
    ∀ (x : B → ℝ), (∑ s, v₀ s * x s = 1) →
    Set.Finite (nonposRoots (standardΦpos M) x)

end TitsCone
