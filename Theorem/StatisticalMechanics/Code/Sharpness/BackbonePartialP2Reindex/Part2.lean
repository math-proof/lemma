/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePartialP2Reindex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneBondwiseOrderedExploration.Part6
import Def.StatisticalMechanics.Code.Sharpness.BackbonePartialP2Reindex.Part2
open SimpleGraph Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace shb_PartialCurrentDynamicSelector

theorem actualMass_nil
    (S : shb_PartialCurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real) (d : shb_ExplorationDomain V) :
    S.actualMass beta J d [] = currentSum d.graph beta J ∅ := by
  unfold actualMass currentSum shb_PartialCurrentDynamicSelector.Fiber
  apply tsum_congr
  intro m
  by_cases hsrc : sources d.graph (ofEdgeFun d.graph m) = ∅
  · have hselect : S.select? d m = some [] :=
      (S.select?_eq_some_nil_iff d m).2 hsrc
    simp [hsrc, hselect]
  · have hselect : S.select? d m ≠ some [] := fun h =>
      hsrc ((S.select?_eq_some_nil_iff d m).1 h)
    simp [hsrc, hselect]

end shb_PartialCurrentDynamicSelector
end
end StatMech.Sharpness
