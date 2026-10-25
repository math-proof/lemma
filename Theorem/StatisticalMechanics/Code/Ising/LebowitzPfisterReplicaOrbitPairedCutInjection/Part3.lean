/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutInjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitCrossToggleMatching.Part8
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPairedCutHallExact
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitExactTagProjection
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPairedCutInjection.Part2
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem LPReplicaEvenLeftBoundary.symmDiff
    {X Y : Finset (LPReplicaCurrentVertex V)}
    (hX : LPReplicaEvenLeftBoundary X)
    (hY : LPReplicaEvenLeftBoundary Y) :
    LPReplicaEvenLeftBoundary (X ∆ Y) := by
  let A := X ∩ lpReplicaCurrentLeftSide
  let B := Y ∩ lpReplicaCurrentLeftSide
  have hinter : (X ∆ Y) ∩ lpReplicaCurrentLeftSide = A ∆ B := by
    ext x
    simp only [A, B, Finset.mem_inter, Finset.mem_symmDiff]
    tauto
  have hdisj : Disjoint (A \ B) (B \ A) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    exact (Finset.mem_sdiff.mp hy).2 (Finset.mem_sdiff.mp hx).1
  have hcard : (A ∆ B).card = (A \ B).card + (B \ A).card := by
    rw [show A ∆ B = (A \ B) ∪ (B \ A) by
      ext x
      simp only [Finset.mem_symmDiff, Finset.mem_union, Finset.mem_sdiff]]
    exact Finset.card_union_of_disjoint hdisj
  change Even A.card at hX
  change Even B.card at hY
  rcases hX with ⟨a, ha⟩
  rcases hY with ⟨b, hb⟩
  have hA := Finset.card_sdiff_add_card_inter A B
  have hB := Finset.card_sdiff_add_card_inter B A
  rw [Finset.inter_comm B A] at hB
  rw [LPReplicaEvenLeftBoundary, hinter, hcard]
  refine ⟨a + b - (A ∩ B).card, ?_⟩
  omega


theorem lpReplica_doubledBoundary_evenLeft
    (X : Finset (LPReplicaCurrentVertex V)) (hX : Even X.card) :
    LPReplicaEvenLeftBoundary
      (X ∆ X.map lpReplicaCurrentReflect.toEmbedding) :=
  lpReplica_even_card_half_symmDiff_reflect_inter_leftSide X hX


theorem lpReplica_evenLeft_after_doubledBoundary
    (A X : Finset (LPReplicaCurrentVertex V))
    (hA : LPReplicaEvenLeftBoundary A) (hX : Even X.card) :
    LPReplicaEvenLeftBoundary
      (A ∆ (X ∆ X.map lpReplicaCurrentReflect.toEmbedding)) :=
  hA.symmDiff (lpReplica_doubledBoundary_evenLeft X hX)


theorem lpReplica_doubledThenSeam_targetBoundaries
    (Si Sj T Sk D : Finset (LPReplicaCurrentVertex V))
    (hD : D = Si ∆ Sk) :
    D ∆ Sk = Si ∧
      ((Si ∆ Sj ∆ T) ∆ D) ∆ Sk = Sj ∆ T := by
  subst D
  constructor <;>
    ext x <;>
    simp only [Finset.mem_symmDiff] <;>
    tauto


theorem lpReplicaBalancedComponentBoundary_ne_seam_symmDiff_ghost
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (B : Finset (LPReplicaCurrentVertex V))
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (hgate : LPReplicaRowGate G sites m B ∅ tag)
    (i : I) :
    lpReplicaBalancedComponentBoundary G sites m B ∅ tag ≠
      lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1 := by
  intro hboundary
  have htarget : (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∈
      lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingGhostSource lpReplicaCurrentGhost0
          lpReplicaCurrentGhost1 := by
    simp [lpMatchingSeamSource, lpMatchingGhostSource,
      lpReplicaCurrentLeft, lpReplicaCurrentRight,
      lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
      Finset.mem_symmDiff]
  have hsource : (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∈
      lpReplicaBalancedComponentBoundary G sites m B ∅ tag := by
    rwa [hboundary]
  change (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∈
    (B ∩ StatMech.Sharpness.RandomCurrent.compOf
      (StatMech.Sharpness.FluxEdgeCopy.endsM
        (lpReplicaCurrentGraph G sites) m)
      (lpReplicaRowCopies G sites m tag false)
      lpReplicaCurrentGhost1) ∆ ∅ at hsource
  simp [Finset.mem_symmDiff,
    StatMech.Sharpness.RandomCurrent.mem_compOf] at hsource
  exact hgate.2.2.1
    (StatMech.Sharpness.RandomCurrent.connK_symm _ _ hsource.2)


theorem lpReplicaRowGate_rightPairedCut_thenSeam
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (Si Sj T Sk : Finset (LPReplicaCurrentVertex V))
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (hgate : LPReplicaRowGate G sites m ∅ (Si ∆ Sj ∆ T) tag)
    (cut : LPReplicaRightCoupledPairedCut
      G sites m (Si ∆ Sj ∆ T) tag)
    (hD : cut.half ∆ cut.half.map lpReplicaCurrentReflect.toEmbedding =
      Si ∆ Sk)
    (Q : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites)
      (lpReplicaCollisionProfile G sites
        (StatMech.Sharpness.FluxEdgeCopy.profileFlux
          (lpReplicaCurrentGraph G sites) m
          (Finset.univ \ cut.selector))
        (StatMech.Sharpness.FluxEdgeCopy.profileFlux
          (lpReplicaCurrentGraph G sites) m cut.selector))))
    (hfalse : StatMech.Sharpness.RandomCurrent.sources
      (StatMech.Sharpness.FluxEdgeCopy.endsM
        (lpReplicaCurrentGraph G sites)
        (lpReplicaCollisionProfile G sites
          (StatMech.Sharpness.FluxEdgeCopy.profileFlux
            (lpReplicaCurrentGraph G sites) m
            (Finset.univ \ cut.selector))
          (StatMech.Sharpness.FluxEdgeCopy.profileFlux
            (lpReplicaCurrentGraph G sites) m cut.selector)))
      (Q.filter fun c =>
        ((lpReplicaCoupledReflectToggleTagRaw
          G sites m cut.selector tag) c).2 = false) = Sk)
    (htrue : StatMech.Sharpness.RandomCurrent.sources
      (StatMech.Sharpness.FluxEdgeCopy.endsM
        (lpReplicaCurrentGraph G sites)
        (lpReplicaCollisionProfile G sites
          (StatMech.Sharpness.FluxEdgeCopy.profileFlux
            (lpReplicaCurrentGraph G sites) m
            (Finset.univ \ cut.selector))
          (StatMech.Sharpness.FluxEdgeCopy.profileFlux
            (lpReplicaCurrentGraph G sites) m cut.selector)))
      (Q.filter fun c =>
        ((lpReplicaCoupledReflectToggleTagRaw
          G sites m cut.selector tag) c).2 = true) = ∅)
    (hdisc0 : ¬ StatMech.Sharpness.RandomCurrent.connK
      (StatMech.Sharpness.FluxEdgeCopy.endsM
        (lpReplicaCurrentGraph G sites)
        (lpReplicaCollisionProfile G sites
          (StatMech.Sharpness.FluxEdgeCopy.profileFlux
            (lpReplicaCurrentGraph G sites) m
            (Finset.univ \ cut.selector))
          (StatMech.Sharpness.FluxEdgeCopy.profileFlux
            (lpReplicaCurrentGraph G sites) m cut.selector)))
      (lpReplicaRowCopies G sites
        (lpReplicaCollisionProfile G sites
          (StatMech.Sharpness.FluxEdgeCopy.profileFlux
            (lpReplicaCurrentGraph G sites) m
            (Finset.univ \ cut.selector))
          (StatMech.Sharpness.FluxEdgeCopy.profileFlux
            (lpReplicaCurrentGraph G sites) m cut.selector))
        (lpReplicaToggleRows G sites _ Q
          (lpReplicaCoupledReflectToggleTagRaw
            G sites m cut.selector tag)) false)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1)
    (hdisc1 : ¬ StatMech.Sharpness.RandomCurrent.connK
      (StatMech.Sharpness.FluxEdgeCopy.endsM
        (lpReplicaCurrentGraph G sites)
        (lpReplicaCollisionProfile G sites
          (StatMech.Sharpness.FluxEdgeCopy.profileFlux
            (lpReplicaCurrentGraph G sites) m
            (Finset.univ \ cut.selector))
          (StatMech.Sharpness.FluxEdgeCopy.profileFlux
            (lpReplicaCurrentGraph G sites) m cut.selector)))
      (lpReplicaRowCopies G sites
        (lpReplicaCollisionProfile G sites
          (StatMech.Sharpness.FluxEdgeCopy.profileFlux
            (lpReplicaCurrentGraph G sites) m
            (Finset.univ \ cut.selector))
          (StatMech.Sharpness.FluxEdgeCopy.profileFlux
            (lpReplicaCurrentGraph G sites) m cut.selector))
        (lpReplicaToggleRows G sites _ Q
          (lpReplicaCoupledReflectToggleTagRaw
            G sites m cut.selector tag)) true)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) :
    LPReplicaRowGate G sites
      (lpReplicaCollisionProfile G sites
        (StatMech.Sharpness.FluxEdgeCopy.profileFlux
          (lpReplicaCurrentGraph G sites) m
          (Finset.univ \ cut.selector))
        (StatMech.Sharpness.FluxEdgeCopy.profileFlux
          (lpReplicaCurrentGraph G sites) m cut.selector))
      Si (Sj ∆ T)
      (lpReplicaToggleRows G sites _ Q
        (lpReplicaCoupledReflectToggleTagRaw
          G sites m cut.selector tag)) := by
  let target := lpReplicaCollisionProfile G sites
    (StatMech.Sharpness.FluxEdgeCopy.profileFlux
      (lpReplicaCurrentGraph G sites) m (Finset.univ \ cut.selector))
    (StatMech.Sharpness.FluxEdgeCopy.profileFlux
      (lpReplicaCurrentGraph G sites) m cut.selector)
  let moved := lpReplicaCoupledReflectToggleTagRaw
    G sites m cut.selector tag
  let D := cut.half ∆ cut.half.map lpReplicaCurrentReflect.toEmbedding
  have hpaired : LPReplicaRowGate G sites target D
      ((Si ∆ Sj ∆ T) ∆ D) moved := by
    simpa only [target, moved, D] using
      lpReplicaRowGate_rightCoupledPairedCut
        G sites m (Si ∆ Sj ∆ T) tag hgate cut
  have htoggled := lpReplicaRowGate_toggle G sites target D
    ((Si ∆ Sj ∆ T) ∆ D) moved Q hpaired htrue hdisc0 hdisc1
  dsimp only at htoggled
  rw [hfalse] at htoggled
  have hb := lpReplica_doubledThenSeam_targetBoundaries Si Sj T Sk D (by
    simpa only [D] using hD)
  rw [hb.1, hb.2] at htoggled
  exact htoggled


theorem LPReplicaRightCoupledPairedCut.half_card_even
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (B : Finset (LPReplicaCurrentVertex V))
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (cut : LPReplicaRightCoupledPairedCut G sites m B tag) :
    Even cut.half.card := by
  have h := StatMech.Walls.gc7_total_handshake_edgeCopy
    (G := lpReplicaCurrentGraph G sites) m
    (lpReplicaCurrentCopies G sites m tag false false ∩ cut.selector)
  rw [cut.falseSource0] at h
  exact h


theorem LPReplicaRightCoupledPairedCut.doubledHalf_ne_seamSource
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (B : Finset (LPReplicaCurrentVertex V))
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (cut : LPReplicaRightCoupledPairedCut G sites m B tag)
    (i : I) :
    cut.half ∆ cut.half.map lpReplicaCurrentReflect.toEmbedding ≠
      lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i := by
  intro hD
  have heven := lpReplica_even_card_half_symmDiff_reflect_inter_leftSide
    cut.half (cut.half_card_even G sites m B tag)
  have hseam :
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∩
        lpReplicaCurrentLeftSide) =
      {lpReplicaCurrentLeft sites i} := by
    ext x
    rcases x with (x | b)
    · rcases x with x | x <;>
        simp [lpMatchingSeamSource, lpReplicaCurrentLeft,
          lpReplicaCurrentRight, lpReplicaCurrentLeftSide,
          lpReplicaCurrentLeftEmbedding, lpReplicaCurrentGhost0,
          Finset.mem_symmDiff]
    · cases b <;>
        simp [lpMatchingSeamSource, lpReplicaCurrentLeft,
          lpReplicaCurrentRight, lpReplicaCurrentLeftSide,
          lpReplicaCurrentLeftEmbedding, lpReplicaCurrentGhost0,
          Finset.mem_symmDiff]
  rw [hD, hseam] at heven
  norm_num at heven

set_option maxHeartbeats 4000000 in


theorem lpReplicaOffdiagDecoratedSourceSlotState_fixedRowGateData
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    let B := lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
      lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
      lpMatchingGhostSource
        (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
        lpReplicaCurrentGhost1
    let hfixed : B.map lpReplicaCurrentReflect.toEmbedding = B := by
      simpa only [B] using
        lpReplicaCurrentReflect_offdiagSource G sites i j
    let d := lpReplicaDecoratedOrbitAtomFixedRowGateData
      G sites ∅ B q hfixed z
    lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z =
      lpReplicaOrbitFourColorSlotStateOfTag G sites q z.1.1.1
        z.1.1.2 z.2.2 d.1 := by
  dsimp only
  unfold lpReplicaOffdiagDecoratedSourceSlotState
    lpReplicaOrientedFourColorSlotState
    lpReplicaOrbitFourColorSlotStateOfTag
    lpReplicaDecoratedOrbitAtomFixedRowGateData
    lpReplicaOrientedFourColorTag
  rfl


end
end StatMech.Ising
