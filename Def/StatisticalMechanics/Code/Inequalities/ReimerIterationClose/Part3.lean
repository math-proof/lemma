/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerIterationClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyProve3.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompressLib.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyProve2.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompression.Part5
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerEndpointProve.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.Reimer.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerIterationClose.Part3
open Finset MeasureTheory
open scoped NNReal FinsetFamily


namespace StatMech

open ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


def rit_BoxDownCompMono (α : Type*) [Fintype α] [DecidableEq α] : Prop :=
  ∀ (w : α → Bool → ℝ), (∀ x b, 0 ≤ w x b) → (∀ x, w x false = w x true) →
    ∀ (i : α) (𝒜 ℬ : Finset (Finset α)),
      wprob w (disjointOccurrence (familyEvent 𝒜) (familyEvent ℬ))
        ≤ wprob w (disjointOccurrence (familyEvent (Down.compression i 𝒜))
            (familyEvent (Down.compression i ℬ)))


end StatMech
