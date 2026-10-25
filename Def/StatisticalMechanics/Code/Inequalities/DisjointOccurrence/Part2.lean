/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/DisjointOccurrence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Inequalities.DisjointOccurrence


namespace StatMech

open ConfigSpace

variable {E : Type*}


def OccursOn (A : Set (ConfigSpace E)) (K : Set E) (ω : ConfigSpace E) : Prop :=
  ∀ ω', agreeOn K ω ω' → ω' ∈ A


end StatMech
