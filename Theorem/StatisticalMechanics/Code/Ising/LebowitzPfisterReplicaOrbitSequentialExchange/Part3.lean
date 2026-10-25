/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitSequentialExchange.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedSourceTrace.Part3
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitExactTagSlotMove
import Abbrev.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitSequentialExchange
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.RandomCurrent

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem LPReplicaRightCoupledPairedCut.falseSource0
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (B : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (cut : LPReplicaRightCoupledPairedCut G sites m B tag) :
    StatMech.Sharpness.RandomCurrent.sources
      (endsM (lpReplicaCurrentGraph G sites) m)
      (lpReplicaCurrentCopies G sites m tag false false ∩ cut.selector) =
        cut.half := by
  simpa only [lpReplicaCurrentCopies_swapRowsTag, Bool.not_true] using
    LPReplicaCoupledPairedCut.falseSource1 cut


theorem LPReplicaRightCoupledPairedCut.falseSource1
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (B : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (cut : LPReplicaRightCoupledPairedCut G sites m B tag) :
    StatMech.Sharpness.RandomCurrent.sources
      (endsM (lpReplicaCurrentGraph G sites) m)
      (lpReplicaCurrentCopies G sites m tag true false ∩ cut.selector) =
        cut.half := by
  simpa only [lpReplicaCurrentCopies_swapRowsTag, Bool.not_false] using
    LPReplicaCoupledPairedCut.falseSource0 cut


theorem LPReplicaRightCoupledPairedCut.trueSource0
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (B : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (cut : LPReplicaRightCoupledPairedCut G sites m B tag) :
    StatMech.Sharpness.RandomCurrent.sources
      (endsM (lpReplicaCurrentGraph G sites) m)
      (lpReplicaCurrentCopies G sites m tag false true ∩ cut.selector) =
        cut.trueHalf := by
  simpa only [lpReplicaCurrentCopies_swapRowsTag, Bool.not_true] using
    LPReplicaCoupledPairedCut.trueSource1 cut


theorem LPReplicaRightCoupledPairedCut.trueSource1
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (B : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (cut : LPReplicaRightCoupledPairedCut G sites m B tag) :
    StatMech.Sharpness.RandomCurrent.sources
      (endsM (lpReplicaCurrentGraph G sites) m)
      (lpReplicaCurrentCopies G sites m tag true true ∩ cut.selector) =
        cut.trueHalf.map lpReplicaCurrentReflect.toEmbedding := by
  simpa only [lpReplicaCurrentCopies_swapRowsTag, Bool.not_false] using
    LPReplicaCoupledPairedCut.trueSource0 cut


theorem lpReplicaCoupledReflectToggleTagRaw_swapRows
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    lpReplicaCoupledReflectToggleTagRaw G sites m P
        (lpReplicaSwapRowsTag tag) =
      lpReplicaSwapRowsTag
        (lpReplicaCoupledReflectToggleTagRaw G sites m P tag) := by
  funext d
  unfold lpReplicaCoupledReflectToggleTagRaw
    lpReplicaPartialReflectTagRaw lpReplicaToggleRows
    lpReplicaSwapRowsTag
  by_cases hc : (lpReplicaPartialReflectCopyEquivRaw
      G sites m P).symm d ∈ P <;> simp [hc]


theorem lpReplicaSwapRowsTag_coupledReflectToggleTagRaw_swapRows
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    lpReplicaSwapRowsTag
        (lpReplicaCoupledReflectToggleTagRaw G sites m P
          (lpReplicaSwapRowsTag tag)) =
      lpReplicaCoupledReflectToggleTagRaw G sites m P tag := by
  rw [lpReplicaCoupledReflectToggleTagRaw_swapRows]
  exact lpReplicaSwapRowsTag_involutive G sites _ _


theorem LPReplicaCoupledPairedCut.half_eq_empty_of_row1False_empty
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (B : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (cut : LPReplicaCoupledPairedCut G sites m B tag)
    (hempty : lpReplicaCurrentCopies G sites m tag true false = ∅) :
    cut.half = ∅ := by
  rw [← cut.falseSource1, hempty]
  ext x
  simp [StatMech.Sharpness.RandomCurrent.mem_sources,
    StatMech.Sharpness.RandomCurrent.degK]


theorem LPReplicaCoupledPairedCut.balancedComponentBoundary_eq_empty
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (B : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (hgate : LPReplicaRowGate G sites m B ∅ tag)
    (cut : LPReplicaCoupledPairedCut G sites m B tag)
    (hselector : cut.selector =
      lpReplicaBalancedComponentSelector G sites m tag) :
    lpReplicaBalancedComponentBoundary G sites m B ∅ tag = ∅ := by
  have hs := lpReplicaBalancedComponentSelector_rowCurrentSources
    G sites m B tag hgate
  have h0 := cut.falseSource0
  have h1 := cut.falseSource1
  rw [hselector] at h0 h1
  exact hs.1.symm.trans (h0.trans (h1.symm.trans hs.2.1))


theorem LPReplicaCoupledPairedCut.doubledHalf_eq_empty_of_balancedSelector
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (B : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (hgate : LPReplicaRowGate G sites m B ∅ tag)
    (cut : LPReplicaCoupledPairedCut G sites m B tag)
    (hselector : cut.selector =
      lpReplicaBalancedComponentSelector G sites m tag) :
    cut.half ∆ cut.half.map lpReplicaCurrentReflect.toEmbedding = ∅ := by
  have hs := lpReplicaBalancedComponentSelector_rowCurrentSources
    G sites m B tag hgate
  have h1 := cut.falseSource1
  rw [hselector] at h1
  have hhalf : cut.half = ∅ := h1.symm.trans hs.2.1
  rw [hhalf]
  simp


theorem lpReplicaRowGate_coupledPairedCut
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (B : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (hgate : LPReplicaRowGate G sites m B ∅ tag)
    (cut : LPReplicaCoupledPairedCut G sites m B tag) :
    let D := cut.half ∆
      cut.half.map lpReplicaCurrentReflect.toEmbedding
    LPReplicaRowGate G sites
      (lpReplicaCollisionProfile G sites
        (profileFlux (lpReplicaCurrentGraph G sites) m
          (Finset.univ \ cut.selector))
        (profileFlux (lpReplicaCurrentGraph G sites) m cut.selector))
      (B ∆ D) D
      (lpReplicaCoupledReflectToggleTagRaw G sites m cut.selector tag) := by
  dsimp only
  have h := lpReplicaRowGate_coupledReflectToggle
    G sites m cut.selector B ∅ cut.half cut.half
      (cut.trueHalf.map lpReplicaCurrentReflect.toEmbedding) cut.trueHalf
      tag hgate cut.falseSource0 cut.falseSource1 cut.trueSource0
      cut.trueSource1 rfl cut.row0Disconn cut.row1Disconn
  have hleft : (B ∆ cut.half) ∆
      cut.half.map lpReplicaCurrentReflect.toEmbedding =
        B ∆ (cut.half ∆
          cut.half.map lpReplicaCurrentReflect.toEmbedding) := by
    ext x
    simp only [Finset.mem_symmDiff]
    tauto
  have hright : (∅ ∆ cut.half) ∆
      cut.half.map lpReplicaCurrentReflect.toEmbedding =
        cut.half ∆ cut.half.map lpReplicaCurrentReflect.toEmbedding := by
    ext x
    simp [Finset.mem_symmDiff]
  rw [← hleft, ← hright]
  exact h


theorem lpReplicaRowGate_rightCoupledPairedCut
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (B : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (hgate : LPReplicaRowGate G sites m ∅ B tag)
    (cut : LPReplicaRightCoupledPairedCut G sites m B tag) :
    let D := cut.half ∆
      cut.half.map lpReplicaCurrentReflect.toEmbedding
    LPReplicaRowGate G sites
      (lpReplicaCollisionProfile G sites
        (profileFlux (lpReplicaCurrentGraph G sites) m
          (Finset.univ \ cut.selector))
        (profileFlux (lpReplicaCurrentGraph G sites) m cut.selector))
      D (B ∆ D)
      (lpReplicaCoupledReflectToggleTagRaw G sites m cut.selector tag) := by
  dsimp only
  let target := lpReplicaCollisionProfile G sites
    (profileFlux (lpReplicaCurrentGraph G sites) m
      (Finset.univ \ cut.selector))
    (profileFlux (lpReplicaCurrentGraph G sites) m cut.selector)
  let movedSwap := lpReplicaCoupledReflectToggleTagRaw
    G sites m cut.selector (lpReplicaSwapRowsTag tag)
  let D := cut.half ∆
    cut.half.map lpReplicaCurrentReflect.toEmbedding
  have hswapped : LPReplicaRowGate G sites m B ∅
      (lpReplicaSwapRowsTag tag) :=
    lpReplicaRowGate_swapRows G sites m ∅ B tag hgate
  have hleft : LPReplicaRowGate G sites target (B ∆ D) D movedSwap := by
    simpa only [target, movedSwap, D] using
      lpReplicaRowGate_coupledPairedCut G sites m B
        (lpReplicaSwapRowsTag tag) hswapped cut
  have hright : LPReplicaRowGate G sites target D (B ∆ D)
      (lpReplicaSwapRowsTag movedSwap) :=
    lpReplicaRowGate_swapRows G sites target (B ∆ D) D movedSwap hleft
  simpa only [target, movedSwap, D,
    lpReplicaSwapRowsTag_coupledReflectToggleTagRaw_swapRows] using hright


theorem lpReplica_half_symmDiff_reflect_fixed
    (X : Finset (LPReplicaCurrentVertex V)) :
    (X ∆ X.map lpReplicaCurrentReflect.toEmbedding).map
        lpReplicaCurrentReflect.toEmbedding =
      X ∆ X.map lpReplicaCurrentReflect.toEmbedding := by
  rw [lpReplica_map_symmDiff,
    lpReplicaCurrentReflect_map_involutive, symmDiff_comm]


end
end StatMech.Ising
