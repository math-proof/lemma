/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalDualEquiv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalDualGeometry.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalDualEquiv.Part6
open scoped symmDiff
open Finset


namespace StatMech.FrontierA

noncomputable section

noncomputable def cubicalClosedSurfaceAnchoredEquiv
    {a b c : Nat} (hb : 0 < b) (hc : 0 < c) :
    ClosedCubicalSurface a b c ≃
      AnchoredConfig (CubicalDualVertex a b c) none :=
  (cubicalVolumeSurfaceEquiv hb hc).symm.trans cellFinsetAnchoredEquiv

end
end StatMech.FrontierA
