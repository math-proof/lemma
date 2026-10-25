/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRFinite.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.DisjointOccurrence.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRFinite.Part4


namespace StatMech.FrontierA

open ConfigSpace

variable {E : Type*} [Fintype E] [DecidableEq E]


noncomputable def functionalDisjointMaxAt (f g : ConfigSpace E → ℝ)
    (omega eta : ConfigSpace E) : ℝ :=
  (disjointCoordinatePairs E).sup' (disjointCoordinatePairs_nonempty (E := E))
    fun pair => cylinderMin f pair.1 omega * cylinderMin g pair.2 eta


noncomputable def functionalDisjointMax (f g : ConfigSpace E → ℝ)
    (omega : ConfigSpace E) : ℝ :=
  functionalDisjointMaxAt f g omega omega


def dualDisjointOccurrence (A B : Set (ConfigSpace E)) :
    Set (ConfigSpace E × ConfigSpace E) :=
  {pair | ∃ K L : Set E, Disjoint K L ∧
    OccursOn A K pair.1 ∧ OccursOn B L pair.2}

end StatMech.FrontierA
