/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalDualEquiv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalDualGeometry.Part2
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalDualEquiv.Part2
open scoped symmDiff
open Finset


namespace StatMech.FrontierA

noncomputable section

theorem cubicalVolumeSurface_injective {a b c : Nat} (hc : 0 < c) :
    Function.Injective (cubicalVolumeSurface (a := a) (b := b) (c := c)) := by
  intro S T hst
  have hval := congrArg Subtype.val hst
  change cubicalVolumeBoundary S = cubicalVolumeBoundary T at hval
  have hboundary : cubicalVolumeBoundary (S ∆ T) = ∅ := by
    rw [cubicalVolumeBoundary, gaugeSurfaceBoundary_symmDiff]
    change cubicalVolumeBoundary S ∆ cubicalVolumeBoundary T = ∅
    rw [hval]
    simp
  have hxy : ∀ (i : Fin a) (j : Fin b) (k : Fin c),
      CubicalPlaquette.xy i j k.castSucc ∉ cubicalVolumeBoundary (S ∆ T) := by
    intro i j k
    rw [hboundary]
    simp
  have hempty := volume_eq_empty_of_lowerXY_boundary_not_mem hc (S ∆ T) hxy
  exact Finset.symmDiff_eq_empty.mp hempty

theorem card_closedCubicalSurface_eq_card_cellFinset
    {a b c : Nat} (hb : 0 < b) (hc : 0 < c) :
    Fintype.card (ClosedCubicalSurface a b c) =
      Fintype.card (Finset (CubicalCell a b c)) := by
  apply le_antisymm
  · exact Fintype.card_le_of_injective _
      (cubicalLowerXYTrace_injective hb hc)
  · exact Fintype.card_le_of_injective _
      (cubicalVolumeSurface_injective hc)

end
end StatMech.FrontierA
