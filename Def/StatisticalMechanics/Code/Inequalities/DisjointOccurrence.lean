/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/DisjointOccurrence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace


namespace StatMech

open ConfigSpace

variable {E : Type*}


def agreeOn (K : Set E) (ω ω' : ConfigSpace E) : Prop := ∀ e ∈ K, ω' e = ω e


end StatMech
