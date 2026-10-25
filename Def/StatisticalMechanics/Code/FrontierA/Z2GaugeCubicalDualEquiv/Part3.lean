/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalDualEquiv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalDualGeometry.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalDualEquiv.Part2
open scoped symmDiff
open Finset


namespace StatMech.FrontierA

noncomputable section

noncomputable def cubicalVolumeSurfaceEquiv
    {a b c : Nat} (hb : 0 < b) (hc : 0 < c) :
    Finset (CubicalCell a b c) ≃ ClosedCubicalSurface a b c :=
  Equiv.ofBijective cubicalVolumeSurface
    ((Fintype.bijective_iff_injective_and_card cubicalVolumeSurface).mpr
      ⟨cubicalVolumeSurface_injective hc,
        (card_closedCubicalSurface_eq_card_cellFinset hb hc).symm⟩)

end
end StatMech.FrontierA
