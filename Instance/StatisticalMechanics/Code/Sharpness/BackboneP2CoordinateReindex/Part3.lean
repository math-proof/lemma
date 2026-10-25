/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP2CoordinateReindex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackbonePartialP2Reindex.Part3
import Def.StatisticalMechanics.Code.Sharpness.BackboneP2CoordinateReindex.Part3
open SimpleGraph Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneP2CoordinateReindex

open BackboneLabeledSwitching

open BackbonePartialP2Reindex

variable {H G : SimpleGraph V}


noncomputable instance liftedResidualVacuumDecidable
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V) :
    DecidablePred (liftedResidualVacuum d s) := Classical.decPred _

noncomputable instance liftedResidualFiberDecidable
    (S : shb_PartialCurrentDynamicSelector (V := V))
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) :
    DecidablePred (liftedResidualFiber S d s ss) := Classical.decPred _


end BackboneP2CoordinateReindex
end
end StatMech.Sharpness
