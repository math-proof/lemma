/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexUnitComponentHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairDecoratedHall.Part3
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexUnitComponentHall
open Finset


namespace StatMech.FrontierD

noncomputable section

abbrev BooleanLayer (Component : Type*) [Fintype Component]
    (cardinality : Nat) :=
  {s : Finset Component // s.card = cardinality}


end
end StatMech.FrontierD
