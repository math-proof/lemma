/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneAsymmetricCoordinateCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneConcreteSelectorObstruction
import Def.StatisticalMechanics.Code.Sharpness.BackboneAsymmetricCoordinateCertificate.Part7
open SimpleGraph Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneConcreteSelector

open BackboneDeterminedCutSwitching

open BackbonePartialP2Reindex

open BackboneP2CoordinateReindex

open BackboneP2CoordinateToggleObstruction

open FluxEdgeCopy

variable {D : Type*}


@[simp] theorem BondwiseSegmentProgram.suffixSpec_event
    (P : BondwiseSegmentProgram V)
    (d : shb_ExplorationDomain V)
    (word : List (shb_ExplorationSegment V))
    (m : d.graph.edgeFinset -> Nat) :
    (P.suffixSpec d word).Event d.graph m =
      BondwiseSuffixEvent d.graph P.scan (P.initial d)
        (P.encode d word) P.bit m := rfl


end BackboneConcreteSelector
end
end StatMech.Sharpness
