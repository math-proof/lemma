/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalDualEquiv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalDualGeometry.Part2
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalDualEquiv.Part3
open scoped symmDiff
open Finset


namespace StatMech.FrontierA

noncomputable section

@[simp] theorem cubicalVolumeSurfaceEquiv_apply
    {a b c : Nat} (hb : 0 < b) (hc : 0 < c)
    (S : Finset (CubicalCell a b c)) :
    (cubicalVolumeSurfaceEquiv hb hc S).1 = cubicalVolumeBoundary S :=
  rfl


end
end StatMech.FrontierA
