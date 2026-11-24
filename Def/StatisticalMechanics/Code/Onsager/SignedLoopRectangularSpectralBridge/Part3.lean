module
public import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopRectangularEmbedding.Part4
public import Theorem.StatisticalMechanics.Code.Onsager.KWRectangleWeighted.Part2
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearPolygonBridge.Part2
public import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusCycleTopology.Part2
public import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopRectangularSpectralBridge.Part2
open Finset SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularSpectralBridge.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Onsager

open StatMech.FrontierA

noncomputable section

def ons_rectDualDartSlot {M N : Nat}
    (dart : (ons_rectDualGraph M N).Dart) : ons_RectDart M N :=
  (ons_rectDualVertexSlot dart.fst, ons_rectDualDartDirection4 dart)

end
end StatMech.Onsager
