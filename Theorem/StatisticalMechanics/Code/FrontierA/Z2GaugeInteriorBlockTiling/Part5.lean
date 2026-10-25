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
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeInteriorBlockTiling.Part5
open Finset Filter Topology
open scoped BigOperators symmDiff


namespace StatMech.FrontierA

noncomputable section

theorem cubicalInteriorBlockFull_symmDiff_central
    (L p k : Nat) :
    cubicalInteriorBlockFullSheet L p k ∆
        cubicalInteriorBlockCentralSheet L p k =
      cubicalInteriorBlockFrame L p k := by
  have hsub := cubicalInteriorBlockCentralSheet_subset_full L p k
  ext plaquette
  simp only [Finset.mem_symmDiff, cubicalInteriorBlockFrame,
    Finset.mem_sdiff]
  constructor
  · rintro (⟨hfull, hnot⟩ | ⟨hcentral, hnot⟩)
    · exact ⟨hfull, hnot⟩
    · exact (hnot (hsub hcentral)).elim
  · rintro ⟨hfull, hnot⟩
    exact Or.inl ⟨hfull, hnot⟩

theorem card_cubicalInteriorBlockFrame (L p k : Nat) :
    (cubicalInteriorBlockFrame L p k).card =
      (cubicalInteriorBlockSide L p k) ^ 2 - (k * L) ^ 2 := by
  rw [cubicalInteriorBlockFrame,
    Finset.card_sdiff_of_subset
      (cubicalInteriorBlockCentralSheet_subset_full L p k)]
  congr 1
  · simp [cubicalInteriorBlockFullSheet, pow_two]
  · simp [cubicalInteriorBlockCentralSheet, pow_two]


theorem cubicalInteriorBlockFullDisorderFreeEnergy_le_central_add_frame
    {K : Real} (hK : 0 < K) (L p k : Nat) :
    multibondDisorderFreeEnergy cubicalDualEnds
        (fun _ : CubicalPlaquette
          (cubicalInteriorBlockSide L p k)
          (cubicalInteriorBlockSide L p k)
          (cubicalInteriorBlockSide L p k) => gaugeDualCoupling K)
        (cubicalInteriorBlockFullSheet L p k) <=
      multibondDisorderFreeEnergy cubicalDualEnds
          (fun _ : CubicalPlaquette
            (cubicalInteriorBlockSide L p k)
            (cubicalInteriorBlockSide L p k)
            (cubicalInteriorBlockSide L p k) => gaugeDualCoupling K)
          (cubicalInteriorBlockCentralSheet L p k) +
        2 * (cubicalInteriorBlockFrame L p k).card * gaugeDualCoupling K := by
  let J := fun _ : CubicalPlaquette
    (cubicalInteriorBlockSide L p k)
    (cubicalInteriorBlockSide L p k)
    (cubicalInteriorBlockSide L p k) => gaugeDualCoupling K
  have hdist := multibondDisorderFreeEnergy_sheet_sub_abs_le
    cubicalDualEnds J (cubicalInteriorBlockFullSheet L p k)
      (cubicalInteriorBlockCentralSheet L p k)
  rw [cubicalInteriorBlockFull_symmDiff_central] at hdist
  have hJ : 0 < gaugeDualCoupling K := gaugeDualCoupling_pos hK
  have hone := (le_abs_self
    (multibondDisorderFreeEnergy cubicalDualEnds J
        (cubicalInteriorBlockFullSheet L p k) -
      multibondDisorderFreeEnergy cubicalDualEnds J
        (cubicalInteriorBlockCentralSheet L p k))).trans hdist
  have hsum : (∑ q ∈ cubicalInteriorBlockFrame L p k, |J q|) =
      ((cubicalInteriorBlockFrame L p k).card : Real) *
        gaugeDualCoupling K := by
    simp [J, abs_of_pos hJ]
  rw [hsum] at hone
  dsimp [J] at hone ⊢
  linarith

end
end StatMech.FrontierA
