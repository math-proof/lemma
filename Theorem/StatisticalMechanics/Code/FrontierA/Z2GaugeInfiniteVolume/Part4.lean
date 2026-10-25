/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInfiniteVolume.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalGluing.Part4
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeInfiniteVolume.Part3
open Filter Set Topology
open scoped BigOperators symmDiff


namespace StatMech.FrontierA

noncomputable section

theorem cubicalFixedLoopWilsonSequence_tendsto
    {beta : Real} (hbeta : 0 < beta) (a b : Nat) :
    Tendsto (cubicalFixedLoopWilsonSequence beta a b) atTop
      (nhds (cubicalInfiniteVolumeWilsonExpectation beta a b)) := by
  apply tendsto_atTop_ciSup (cubicalFixedLoopWilsonSequence_mono hbeta.le a b)
  exact ⟨1, fun x ⟨n, hn⟩ => hn ▸
    (cubicalFixedLoopWilsonSequence_mem_Icc hbeta a b n).2⟩

theorem cubicalInfiniteVolumeWilsonExpectation_mem_Icc
    {beta : Real} (hbeta : 0 < beta) (a b : Nat) :
    cubicalInfiniteVolumeWilsonExpectation beta a b ∈ Set.Icc 0 1 := by
  have hlim := cubicalFixedLoopWilsonSequence_tendsto hbeta a b
  constructor
  · exact ge_of_tendsto hlim (Eventually.of_forall fun n =>
      (cubicalFixedLoopWilsonSequence_mem_Icc hbeta a b n).1)
  · exact le_of_tendsto hlim (Eventually.of_forall fun n =>
      (cubicalFixedLoopWilsonSequence_mem_Icc hbeta a b n).2)


theorem cubicalPaddedWilsonExpectation_le_infiniteVolume
    {beta : Real} (hbeta : 0 < beta) (a b lx rx ly ry lz rz : Nat) :
    cubicalPaddedWilsonExpectation beta a b lx rx ly ry lz rz ≤
      cubicalInfiniteVolumeWilsonExpectation beta a b := by
  let N := max lx (max rx (max ly (max ry (max lz rz))))
  have hpad : cubicalPaddedWilsonExpectation beta a b lx rx ly ry lz rz ≤
      cubicalFixedLoopWilsonSequence beta a b N := by
    apply cubicalPaddedWilsonExpectation_mono hbeta.le
    all_goals dsimp [N] <;> omega
  exact hpad.trans (le_ciSup
    (⟨1, fun x ⟨n, hn⟩ => hn ▸
      (cubicalFixedLoopWilsonSequence_mem_Icc hbeta a b n).2⟩)
    N)


theorem cubicalPaddedWilsonExpectation_tendsto_infiniteVolume
    {beta : Real} (hbeta : 0 < beta) (a b : Nat)
    (lx rx ly ry lz rz : Nat → Nat)
    (hlx : Tendsto lx atTop atTop) (hrx : Tendsto rx atTop atTop)
    (hly : Tendsto ly atTop atTop) (hry : Tendsto ry atTop atTop)
    (hlz : Tendsto lz atTop atTop) (hrz : Tendsto rz atTop atTop) :
    Tendsto (fun n => cubicalPaddedWilsonExpectation beta a b
      (lx n) (rx n) (ly n) (ry n) (lz n) (rz n)) atTop
      (nhds (cubicalInfiniteVolumeWilsonExpectation beta a b)) := by
  apply tendsto_order.2
  constructor
  · intro x hx
    have hcanon : ∀ᶠ n : Nat in atTop,
        x < cubicalFixedLoopWilsonSequence beta a b n :=
      (cubicalFixedLoopWilsonSequence_tendsto hbeta a b).eventually
        (Ioi_mem_nhds hx)
    obtain ⟨N, hN⟩ := (eventually_atTop.1 hcanon)
    filter_upwards [hlx.eventually (eventually_ge_atTop N),
      hrx.eventually (eventually_ge_atTop N),
      hly.eventually (eventually_ge_atTop N),
      hry.eventually (eventually_ge_atTop N),
      hlz.eventually (eventually_ge_atTop N),
      hrz.eventually (eventually_ge_atTop N)] with n h1 h2 h3 h4 h5 h6
    exact (hN N le_rfl).trans_le
      (cubicalPaddedWilsonExpectation_mono hbeta.le a b
        h1 h2 h3 h4 h5 h6)
  · intro y hy
    exact Eventually.of_forall fun n =>
      (cubicalPaddedWilsonExpectation_le_infiniteVolume hbeta a b
        (lx n) (rx n) (ly n) (ry n) (lz n) (rz n)).trans_lt hy


theorem cubicalWilsonExpectation_eq_twistedIsingPartitionRatio_of_surface
    {A B C : Nat} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (K : CubicalPlaquette A B C → Real) (hK : ∀ p, 0 < K p)
    (D : Finset (CubicalPlaquette A B C)) :
    gaugeWilsonExpectation cubicalPlaquetteIncidence K
        (gaugeSurfaceBoundary cubicalPlaquetteIncidence D) =
      multibondIsingPartition cubicalDualEnds
          (multibondTwistCoupling (fun p => gaugeDualCoupling (K p)) D) /
        multibondIsingPartition cubicalDualEnds
          (fun p => gaugeDualCoupling (K p)) := by
  calc
    gaugeWilsonExpectation cubicalPlaquetteIncidence K
        (gaugeSurfaceBoundary cubicalPlaquetteIncidence D) =
      (∑ s : AnchoredConfig (CubicalDualVertex A B C) none,
          ∏ p ∈ multibondCut cubicalDualEnds s.1 ∆ D,
            Real.exp (-2 * gaugeDualCoupling (K p))) /
        (∑ s : AnchoredConfig (CubicalDualVertex A B C) none,
          ∏ p ∈ multibondCut cubicalDualEnds s.1,
            Real.exp (-2 * gaugeDualCoupling (K p))) := by
      apply gaugeWilsonExpectation_eq_multibondDisorderRatio_of_sheet
        cubicalPlaquetteIncidence K hK _ D
        (hasWilsonBoundary_gaugeSurfaceBoundary _ _) none cubicalDualEnds
        (cubicalClosedSurfaceAnchoredEquiv hB hC)
      exact multibondCut_cubicalClosedSurfaceAnchoredEquiv hA hB hC
    _ = multibondIsingPartition cubicalDualEnds
          (multibondTwistCoupling (fun p => gaugeDualCoupling (K p)) D) /
        multibondIsingPartition cubicalDualEnds
          (fun p => gaugeDualCoupling (K p)) :=
      (multibondIsing_twist_partition_ratio_eq_disorderRatio
        none cubicalDualEnds (fun p => gaugeDualCoupling (K p)) D).symm


theorem neg_log_cubicalWilsonExpectation_eq_disorderFreeEnergy_of_surface
    {A B C : Nat} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (K : CubicalPlaquette A B C → Real) (hK : ∀ p, 0 < K p)
    (D : Finset (CubicalPlaquette A B C)) :
    -Real.log (gaugeWilsonExpectation cubicalPlaquetteIncidence K
        (gaugeSurfaceBoundary cubicalPlaquetteIncidence D)) =
      multibondDisorderFreeEnergy cubicalDualEnds
        (fun p => gaugeDualCoupling (K p)) D := by
  rw [cubicalWilsonExpectation_eq_twistedIsingPartitionRatio_of_surface
    hA hB hC K hK D]
  unfold multibondDisorderFreeEnergy
  rw [Real.log_div
    (multibondIsingPartition_pos _ _).ne'
    (multibondIsingPartition_pos _ _).ne']
  ring


end
end StatMech.FrontierA
