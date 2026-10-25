/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairExplicitDecoration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairCTypeHall.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairExplicitDecoration.Part4
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexExplicitMarkedSiteProjection
    {T : EvenTorus} {omega eta : SixVertexArrows T} {k : Nat}
    (decoration : SixVertexExplicitMarkedPairDecoration omega eta k) :
    Finset (Bool × T.Vertex) :=
  decoration.1.1.map (Function.Embedding.subtype _)

end
end StatMech.FrontierD
