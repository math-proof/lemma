/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoUnitCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeBondToggle.Part3
open SimpleGraph Finset
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneTwoUnitCertificate

open BackboneConcreteSelector

open BackboneConcreteBondProgram (canonicalEdgeSegment)

open BackboneTwoEdgeBondProgram

open BackboneTwoEdgeBondToggle

open BackboneDeterminedCutSwitching

open BackboneLabeledSwitching

open BackbonePartialP2Reindex

open BackboneP2CoordinateReindex

open FluxEdgeCopy

noncomputable local instance twoUnitCertificateDecidableAdj
    (G : SimpleGraph V) : DecidableRel G.Adj := Classical.decRel _


end BackboneTwoUnitCertificate
end
end StatMech.Sharpness
