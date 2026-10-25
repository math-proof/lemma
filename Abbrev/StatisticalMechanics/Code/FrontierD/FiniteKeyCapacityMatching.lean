/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteKeyCapacityMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexTwoCycleCapacityHall.Part4
open Finset


namespace StatMech.FrontierD

noncomputable section

abbrev FiniteKeyCapacityCopies
    (Key : Type*) (capacity : Key -> Nat) :=
  Sigma fun key : Key => Fin (capacity key)


end
end StatMech.FrontierD
