/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerClose2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.BK.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.Reimer.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerClose2.Part3
open MeasureTheory Finset
open scoped NNReal


namespace StatMech

open ConfigSpace

variable {E : Type*}


def ReimerSliceStep (n : ℕ) : Prop :=
  ∀ (ψ : Fin n → Bool → ℝ),
    (∀ i b, 0 ≤ ψ i b) → (∀ i, ψ i false + ψ i true = 1) →
    ∀ (A B : Set (ConfigSpace (Fin (n + 1)))),
      wprob ψ (disjointOccurrence (slice A false) (slice B false))
          ≤ wprob ψ (disjointOccurrence (slice A false) (slice B true)
                      ∩ disjointOccurrence (slice A true) (slice B false))
      ∧ wprob ψ (disjointOccurrence (slice A false) (slice B true)
                  ∪ disjointOccurrence (slice A true) (slice B false))
          ≤ wprob ψ (slice A true) * wprob ψ (slice B true)


end StatMech
