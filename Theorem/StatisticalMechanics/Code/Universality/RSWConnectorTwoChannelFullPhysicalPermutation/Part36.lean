/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFibreCube.Part3
import Theorem.StatisticalMechanics.Code.Lattice.CollaredWalkCrossing
import Theorem.StatisticalMechanics.Code.TwoDim.ZhangFaithfulExclusive.Part2
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part36
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_collaredVerticalArc_meets_leftRightWalk
    {alpha beta bottom top : Int}
    (hab : alpha < beta) (hbt : bottom ≤ top)
    {x y a b : Site 2}
    (hxBox : x ∈ rect alpha beta bottom top)
    (hyBox : y ∈ rect alpha beta bottom top)
    (V : (hypercubicLattice 2).Walk x y)
    (hVBox : ∀ z ∈ V.support, z ∈ rect alpha beta bottom top)
    (H : (hypercubicLattice 2).Walk a b)
    (haBox : a ∈ rect alpha beta bottom top)
    (hbBox : b ∈ rect alpha beta bottom top)
    (haLeft : a 0 = alpha) (hbRight : b 0 = beta)
    (hHBox : ∀ z ∈ H.support, z ∈ rect alpha beta bottom top)
    (hpre : ∀ z ∈ H.support,
      z ∈ (sw_vertSeg (x 0) bottom (x 1)).support → z ∈ V.support)
    (hpost : ∀ z ∈ H.support,
      z ∈ (sw_vertSeg (y 0) (y 1) top).support → z ∈ V.support) :
    ∃ z ∈ H.support, z ∈ V.support := by
  have hxCoord : (![x 0, x 1] : Site 2) = x := by
    ext i
    fin_cases i <;> simp
  have hyCoord : (![y 0, y 1] : Site 2) = y := by
    ext i
    fin_cases i <;> simp
  let pre : (hypercubicLattice 2).Walk ![x 0, bottom] x :=
    (sw_vertSeg (x 0) bottom (x 1)).copy rfl hxCoord
  let post : (hypercubicLattice 2).Walk y ![y 0, top] :=
    (sw_vertSeg (y 0) (y 1) top).copy hyCoord rfl
  let Vc : (hypercubicLattice 2).Walk
      ![x 0, bottom] ![y 0, top] := (pre.append V).append post
  have hVcBox : ∀ z ∈ Vc.support,
      z ∈ rect alpha beta bottom top := by
    intro z hz
    dsimp only [Vc] at hz
    rw [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with (hzPre | hzV) | hzPost
    · dsimp only [pre] at hzPre
      rw [SimpleGraph.Walk.support_copy, sw_vertSeg_mem_support] at hzPre
      obtain ⟨t, ht, rfl⟩ := hzPre
      rw [Set.mem_uIcc] at ht
      rw [mem_rect] at hxBox ⊢
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    · exact hVBox z hzV
    · dsimp only [post] at hzPost
      rw [SimpleGraph.Walk.support_copy, sw_vertSeg_mem_support] at hzPost
      obtain ⟨t, ht, rfl⟩ := hzPost
      rw [Set.mem_uIcc] at ht
      rw [mem_rect] at hyBox ⊢
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
  have hsep : ArcSeparatingSet {z | z ∈ Vc.support}
      alpha beta bottom top := by
    have hxBounds := (mem_rect.mp hxBox)
    have hyBounds := (mem_rect.mp hyBox)
    exact jec_arcSeparatingSet alpha beta bottom top (x 0) (y 0)
      hab hbt hxBounds.1 hxBounds.2.1 hyBounds.1 hyBounds.2.1
        Vc hVcBox {z | z ∈ Vc.support} (fun _ hz => hz)
  obtain ⟨z, hzH, hzVc⟩ := tpc_two_paths_cross_of_sep hsep
    haBox hbBox haLeft hbRight H hHBox
  change z ∈ Vc.support at hzVc
  dsimp only [Vc] at hzVc
  rw [SimpleGraph.Walk.mem_support_append_iff,
    SimpleGraph.Walk.mem_support_append_iff] at hzVc
  rcases hzVc with (hzPre | hzV) | hzPost
  · refine ⟨z, hzH, hpre z hzH ?_⟩
    simpa [pre, SimpleGraph.Walk.support_copy] using hzPre
  · exact ⟨z, hzH, hzV⟩
  · refine ⟨z, hzH, hpost z hzH ?_⟩
    simpa [post, SimpleGraph.Walk.support_copy] using hzPost


end
end StatMech.Universality
