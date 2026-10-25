/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusConcreteRibbon.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusRibbonClassification
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialClosedCycles.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusConcreteRibbon
open Equiv Finset


namespace StatMech.FrontierD

open StatMech.FrontierA

noncomputable section

variable {T : EvenTorus}


noncomputable def fkRectRibbonSystem (R : FKRectTorus) :
    RibbonPermutationSystem R.EdgeIndex
      (FKMedialBlackDart R.medialTorus) where
  rotation := fkMedialBlackBoundaryPerm (fkRectClosedMedialPairing R)
  edgeFlip := fun e =>
    fkMedialBlackDartSwap (fkRectMedialVertexOfEdge R e)
  edgeFlip_isSwap := fun e => fkMedialBlackDartSwap_isSwap _
  edgeFlip_commute := by
    intro e f hef
    apply fkMedialBlackDartSwap_commute
    intro hv
    apply hef
    exact (fkRectTorusMedialEdgeEquiv R).symm.injective hv


end
end StatMech.FrontierD
