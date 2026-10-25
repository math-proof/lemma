/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/DisjointOccurrence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Inequalities.DisjointOccurrence.Part2


namespace StatMech

open ConfigSpace

variable {E : Type*}


def disjointOccurrence (A B : Set (ConfigSpace E)) : Set (ConfigSpace E) :=
  {ω | ∃ K L : Set E, Disjoint K L ∧ OccursOn A K ω ∧ OccursOn B L ω}


scoped notation3:70 A " □ " B => disjointOccurrence A B


end StatMech
