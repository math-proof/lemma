/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitPhysicalKey.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedUnitSelector.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedUnitPhysicalKey.Part8


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexDegreeTwoSynchronizedComponentBoundaryFinKey_injective
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) :
    Function.Injective
      (sixVertexDegreeTwoSynchronizedComponentBoundaryFinKey homega heta
        hdegree component layer) := by
  intro first second heq
  apply (Fintype.equivFin
    (SixVertexDegreeTwoSynchronizedComponentBoundaryOccurrence homega heta
      hdegree component)).symm.injective
  apply Subtype.ext
  unfold sixVertexDegreeTwoSynchronizedComponentBoundaryFinKey at heq
  cases layer
  · exact (fkColoredBlackDartStrandSlotEquiv
      (alignedRoutingLoopPairing homega heta hdegree false)).injective heq
  · apply (alignedBlackDartLayerSwap homega heta hdegree).injective
    exact (fkColoredBlackDartStrandSlotEquiv
      (alignedRoutingLoopPairing homega heta hdegree true)).injective heq


end
end StatMech.FrontierD
