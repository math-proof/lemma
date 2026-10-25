/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairExplicitDecoration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairCTypeHall.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairExplicitDecoration.Part3
open Finset


namespace StatMech.FrontierD

noncomputable section

abbrev SixVertexExplicitMarkedPairDecoration
    {T : EvenTorus} (omega eta : SixVertexArrows T) (k : Nat) :=
  MarkedBinaryDecoration (SixVertexPairCTypeSite omega eta) k


end
end StatMech.FrontierD
