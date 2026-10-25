/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerFiberClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.Reimer.Part3
open MeasureTheory Finset
open scoped NNReal BigOperators


namespace StatMech

open ConfigSpace

variable {E : Type*}


def DeterminedBy (A : Set (ConfigSpace E)) (K : Set E) : Prop :=
  ∀ ω ω' : ConfigSpace E, agreeOn K ω ω' → (ω ∈ A ↔ ω' ∈ A)


end StatMech
