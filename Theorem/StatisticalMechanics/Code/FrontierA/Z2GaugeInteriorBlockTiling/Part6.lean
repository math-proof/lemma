/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInteriorBlockTiling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeDiagonalBoundaryApproximation.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSheetTiling.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSlabGaugeAudit
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeSurfaceTensionIdentification
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeInteriorBlockTiling.Part6
open Finset Filter Topology
open scoped BigOperators symmDiff


namespace StatMech.FrontierA

noncomputable section

theorem cubicalInteriorBlockBottomSheet_subset_slabComplement
    (L p k : Nat) (hp : 0 < p) :
    cubicalInteriorBlockBottomSheet L p k ⊆
      cubicalInteriorBlockSlabComplement L p k := by
  intro plaquette hplaquette
  rcases Finset.mem_image.mp hplaquette with ⟨ij, _, rfl⟩
  apply Finset.mem_sdiff.mpr
  constructor
  · rw [mem_multibondCut]
    let z0 : Fin (cubicalInteriorBlockSide L p k) :=
      ⟨0, by simp [cubicalInteriorBlockSide]; omega⟩
    have hf : finForward
        (0 : Fin (cubicalInteriorBlockSide L p k + 1)) = some z0 := by
      rw [finForward_eq_some_iff]
      apply Fin.ext
      rfl
    have hb : finBackward
        (0 : Fin (cubicalInteriorBlockSide L p k + 1)) = none :=
      (finBackward_eq_none_iff _).2 rfl
    simp [cubicalDualEnds, hb, hf, cubicalBelowSpin,
      cubicalInteriorBlockHeight, z0, hp]
  · intro htop
    simp only [cubicalXYSheet, Finset.mem_image, Finset.mem_univ,
      true_and] at htop
    obtain ⟨xy, hxy⟩ := htop
    have hz := (CubicalPlaquette.xy.inj hxy).2.2
    have hzval := congrArg Fin.val hz
    simp [cubicalInteriorBlockHeight] at hzval
    omega

end
end StatMech.FrontierA
