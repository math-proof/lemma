/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairExplicitDecoration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairCTypeHall.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairExplicitDecoration
open Finset


namespace StatMech.FrontierD

noncomputable section

abbrev SixVertexPairCTypeSite
    {T : EvenTorus} (omega eta : SixVertexArrows T) :=
  {x : Bool × T.Vertex //
    (if x.1 then eta else omega).IsCType x.2}

end
end StatMech.FrontierD
