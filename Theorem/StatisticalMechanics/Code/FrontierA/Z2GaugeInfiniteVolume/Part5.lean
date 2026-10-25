/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInfiniteVolume.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalGluing.Part4
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeInfiniteVolume.Part4
open Filter Set Topology
open scoped BigOperators symmDiff


namespace StatMech.FrontierA

noncomputable section

theorem gaugeSurfaceBoundary_cubicalPaddedXYSheet
    (a b lx rx ly ry lz rz : Nat) :
    gaugeSurfaceBoundary cubicalPlaquetteIncidence
        (cubicalPaddedXYSheet a b lx rx ly ry lz rz) =
      (cubicalXYLoop (a := a) (b := b) (c := 0) (0 : Fin 1)).map
        (cubicalEdgeChart lx ly lz (by omega) (by omega) (by omega)) := by
  exact gaugeSurfaceBoundary_map
    cubicalPlaquetteIncidence cubicalPlaquetteIncidence
    (cubicalEdgeChart lx ly lz (by omega) (by omega) (by omega))
    (cubicalPlaquetteChart lx ly lz (by omega) (by omega) (by omega))
    (cubicalPlaquetteIncidence_chart lx ly lz (by omega) (by omega) (by omega))
    (cubicalXYSheet (0 : Fin 1))

theorem cubicalPaddedWilsonExpectation_pos
    {beta : Real} (hbeta : 0 < beta) (a b lx rx ly ry lz rz : Nat) :
    0 < cubicalPaddedWilsonExpectation beta a b lx rx ly ry lz rz := by
  unfold cubicalPaddedWilsonExpectation
  apply (gaugeWilsonExpectation_pos_iff_exists_boundary
    cubicalPlaquetteIncidence (fun _ => beta) (fun _ => hbeta) _).mpr
  let D := cubicalPaddedXYSheet a b lx rx ly ry lz rz
  refine ⟨D, ?_⟩
  rw [← gaugeSurfaceBoundary_cubicalPaddedXYSheet]
  exact hasWilsonBoundary_gaugeSurfaceBoundary _ D

theorem cubicalInfiniteVolumeWilsonExpectation_pos
    {beta : Real} (hbeta : 0 < beta) (a b : Nat) :
    0 < cubicalInfiniteVolumeWilsonExpectation beta a b := by
  have hfinite : 0 < cubicalFixedLoopWilsonSequence beta a b 0 := by
    exact cubicalPaddedWilsonExpectation_pos hbeta a b 0 0 0 0 0 0
  have hbdd : BddAbove
      (Set.range (cubicalFixedLoopWilsonSequence beta a b)) :=
    ⟨1, fun x ⟨n, hn⟩ => hn ▸
      (cubicalFixedLoopWilsonSequence_mem_Icc hbeta a b n).2⟩
  exact hfinite.trans_le (le_ciSup hbdd 0)


end
end StatMech.FrontierA
