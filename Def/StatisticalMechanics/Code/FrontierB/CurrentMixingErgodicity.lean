/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentMixingErgodicity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierB.InfiniteCurrentFiniteMarginals
open MeasureTheory Set
open scoped ENNReal symmDiff


namespace StatMech.FrontierB

variable {E H : Type*} [Group H] [MulAction H E]


def CurrentSelfMixing [Countable E]
    (mu : Measure (InfiniteCurrentConfig E)) : Prop :=
  ∀ A ∈ measurableCylinders (fun _ : E => Nat), ∀ epsilon : Real,
    0 < epsilon ->
      ∃ g : H,
        abs (mu.real (A ∩ (currentShift g) ⁻¹' A) - (mu.real A) ^ 2) < epsilon


end StatMech.FrontierB
