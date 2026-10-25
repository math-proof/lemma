/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentOrbit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoComponentStrand.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoUnitComponentOrbitHall.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentOrbit.Part6
open Finset
open scoped symmDiff


namespace StatMech.FrontierD

noncomputable section

structure SixVertexPositiveUnitComponentOrbitData
    (T : EvenTorus) (middle : Fin (T.width + 1)) where
  k : Nat
  base : SixVertexPositiveUnitComponentOrbitBase T middle k

end
end StatMech.FrontierD
