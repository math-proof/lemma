/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/FiniteProperParabolicsInstance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.AffineCoxeter.TitsConeFiniteParabolic.Part4
import Theorem.v1.Atlas.Buildings.code.AffineCoxeter.FiniteProperParabolicsInstance
set_option linter.unusedSectionVars false

open Finset BigOperators CoxeterGroup TitsCone


namespace TitsCone

variable {B : Type*} [DecidableEq B] [Fintype B]

/-- Hypotheses isolating the two key properties of an affine, crystallographic Coxeter system used
in the proofs: (1) coercivity of the form $B$ on every proper parabolic subspace, and
(2) integrality of the coordinates of every positive root in the simple-root basis. -/
structure AffineCoxeterHyp (M : CoxeterMatrix B) : Prop where
  coercive_on_proper_subset :
    ∀ (I : Finset B), I ≠ Finset.univ →
      ∃ (c : ℝ), 0 < c ∧
        ∀ (v : B → ℝ), (∀ s, s ∉ I → v s = 0) →
          c * ∑ b : B, (v b) ^ 2 ≤ CoxeterGroup.bilinForm M v v
  roots_integer_coords :
    ∀ α ∈ standardΦpos M, ∀ b : B, ∃ n : ℤ, α b = ↑n

end TitsCone
