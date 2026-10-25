/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePartialP2Reindex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneBondwiseOrderedExploration.Part6
import Theorem.StatisticalMechanics.Code.Sharpness.BackbonePartialP2Reindex
open SimpleGraph Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace shb_PartialCurrentDynamicSelector

noncomputable def actualMass
    (S : shb_PartialCurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real) : shb_ExplorationFiberMass V :=
  fun d word =>
    ∑' m : d.graph.edgeFinset -> Nat,
      if S.Fiber d word m then weight d.graph beta J (ofEdgeFun d.graph m)
      else 0


end shb_PartialCurrentDynamicSelector
end
end StatMech.Sharpness
