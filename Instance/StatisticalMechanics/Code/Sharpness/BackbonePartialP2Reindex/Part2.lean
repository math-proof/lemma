/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePartialP2Reindex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneBondwiseOrderedExploration.Part6
import Theorem.StatisticalMechanics.Code.Sharpness.BackbonePartialP2Reindex.Part2
open SimpleGraph Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackbonePartialP2Reindex

open FluxEdgeCopy

open BackboneLabeledSwitching

open BackboneDeterminedCutSwitching

variable {D : Type*}

noncomputable local instance partialP2DecidableAdj (H : SimpleGraph V) :
    DecidableRel H.Adj := Classical.decRel _


end BackbonePartialP2Reindex
end
end StatMech.Sharpness
