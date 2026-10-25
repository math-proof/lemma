/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairExplicitDecoration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairCTypeHall.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairExplicitDecoration.Part5
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexExplicitUnresolvedSiteFinset
    {T : EvenTorus} {omega eta : SixVertexArrows T} {k : Nat}
    (decoration : SixVertexExplicitMarkedPairDecoration omega eta k) :
    Finset (Bool × T.Vertex) :=
  Finset.univ.filter fun x =>
    sixVertexExplicitMarkedPartialPairing decoration x.1 x.2 = none

end
end StatMech.FrontierD
