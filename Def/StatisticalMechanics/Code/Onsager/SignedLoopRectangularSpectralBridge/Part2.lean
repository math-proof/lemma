/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularSpectralBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopRectangularEmbedding.Part4
import Theorem.StatisticalMechanics.Code.Onsager.KWRectangleWeighted.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearPolygonBridge.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusCycleTopology.Part2
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopRectangularSpectralBridge
open Finset SimpleGraph


namespace StatMech.Onsager

open StatMech.FrontierA

noncomputable section

def ons_rectDualVertexSlot {M N : Nat}
    (vertex : ons_RectDualVertex M N) : ons_RectVertex M N :=
  ((vertex.1.val : ZMod (M + 1)), (vertex.2.val : ZMod (N + 1)))

end
end StatMech.Onsager
