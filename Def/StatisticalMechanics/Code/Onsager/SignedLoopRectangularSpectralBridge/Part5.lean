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
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopRectangularSpectralBridge.Part4
open Finset SimpleGraph


namespace StatMech.Onsager

open StatMech.FrontierA

noncomputable section

noncomputable def ons_rectDualWalkExponent (M N : Nat)
    (edgeWeight : Sym2 (ons_RectDualVertex M N) → Complex) : Complex :=
  ∑' n : Nat,
    (∑ walk : Fin (n + 1) → (ons_rectDualGraph M N).Dart,
      ∏ k : Fin (n + 1),
        kwGraphTransition (ons_rectDualGraph M N) edgeWeight
          (ons_rectDualStraightLineEmbedding M N).turnPhase
          (walk k) (walk (k + 1))) / (n + 1)


noncomputable def ons_rectDualEdgeSignDefect (M N : Nat)
    (defect : Sym2 (ons_RectDualVertex M N) → Prop)
    [DecidablePred defect] (q : Real)
    (edge : Sym2 (ons_RectDualVertex M N)) : Complex :=
  if defect edge then -(q : Complex) else (q : Complex)

end
end StatMech.Onsager
