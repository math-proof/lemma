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
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeInteriorBlockTiling.Part4
open Finset Filter Topology
open scoped BigOperators symmDiff


namespace StatMech.FrontierA

noncomputable section

theorem cubicalInteriorBlockCentralSheet_subset_full
    (L p k : Nat) :
    cubicalInteriorBlockCentralSheet L p k ⊆
      cubicalInteriorBlockFullSheet L p k := by
  intro plaquette hpq
  cases plaquette with
  | xy x y z =>
      simp only [cubicalInteriorBlockCentralSheet, cubicalXYSheet,
        Finset.mem_map, Finset.mem_image, Finset.mem_univ, true_and] at hpq
      obtain ⟨_, ⟨ij, _, rfl⟩, hpq⟩ := hpq
      unfold cubicalInteriorBlockFullSheet cubicalXYSheet
      apply Finset.mem_image.mpr
      refine ⟨((finOffsetEmbedding p (by simp [cubicalInteriorBlockSide]) ij.1),
        (finOffsetEmbedding p (by simp [cubicalInteriorBlockSide]) ij.2)),
        Finset.mem_univ _, ?_⟩
      change CubicalPlaquette.xy _ _ _ = CubicalPlaquette.xy x y z
      rw [CubicalPlaquette.xy.injEq]
      exact ⟨(CubicalPlaquette.xy.inj hpq).1,
        (CubicalPlaquette.xy.inj hpq).2.1,
        (CubicalPlaquette.xy.inj hpq).2.2.trans (by
          apply Fin.ext
          rfl)⟩
  | xz x y z =>
      simp [cubicalInteriorBlockCentralSheet, cubicalXYSheet,
        cubicalPlaquetteChart] at hpq
  | yz x y z =>
      simp [cubicalInteriorBlockCentralSheet, cubicalXYSheet,
        cubicalPlaquetteChart] at hpq

end
end StatMech.FrontierA
