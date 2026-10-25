/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Reimer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.BK.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.DisjointOccurrence.Part3
open MeasureTheory Finset
open scoped NNReal


namespace StatMech

open ConfigSpace

variable {E F : Type*}


def ReimerWprobCore : Prop :=
  ∀ (n : ℕ) (φ : Fin n → Bool → ℝ),
    (∀ i b, 0 ≤ φ i b) → (∀ i, φ i false + φ i true = 1) →
    ∀ (A B : Set (ConfigSpace (Fin n))),
      wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B


end StatMech
