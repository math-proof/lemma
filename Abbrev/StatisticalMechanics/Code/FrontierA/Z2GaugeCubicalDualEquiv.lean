/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalDualEquiv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalDualGeometry.Part2
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalDualEquiv
open scoped symmDiff
open Finset


namespace StatMech.FrontierA

noncomputable section

abbrev ClosedCubicalSurface (a b c : Nat) :=
  {A : Finset (CubicalPlaquette a b c) //
    A ∈ gaugeClosedSurfaceFamily cubicalPlaquetteIncidence}

end
end StatMech.FrontierA
