/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldBoundaryBandPadding.Part3
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldExclusion
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldDeepTemplateGridAssembly
import Structure.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldBoundaryBandAssembly.Part3
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


variable {W : Type*} [DecidableEq W] [Countable W]
  {Pdual : PeriodicGraph W}


theorem PeriodicPlaneEmbedding.NormalBoundaryBandSeed.left_tangential
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    {S : Finset V} {margin : Nat} {p : Real}
    (seed : E.NormalBoundaryBandSeed mu S margin p)
    (tangent : Fin (margin + 1) → Int) (i : Fin (margin + 1)) :
    let shift := seed.baseLeft + horizontalShift i.val +
      verticalShift (tangent i)
    P.shift shift '' (S : Set V) ⊆
        E.rectVertices 0 seed.radiusLeft
          ((tangent i : Real) - seed.radiusLeft)
          ((tangent i : Real) + seed.radiusLeft) ∧
      p < mu.real (E.rectSideConnectionEvent 0 seed.radiusLeft
        ((tangent i : Real) - seed.radiusLeft)
        ((tangent i : Real) + seed.radiusLeft)
        (P.shift shift '' (S : Set V))
        (E.rectLeftBoundaryVertices 0 seed.radiusLeft
          ((tangent i : Real) - seed.radiusLeft)
          ((tangent i : Real) + seed.radiusLeft))) := by
  dsimp only
  let base := seed.baseLeft + horizontalShift i.val
  let z := verticalShift (tangent i)
  have hz0 : (z 0 : Real) = 0 := by simp [z]
  have hz1 : (z 1 : Real) = tangent i := by simp [z]
  have himage : P.shift z '' (P.shift base '' (S : Set V)) =
      P.shift (base + verticalShift (tangent i)) '' (S : Set V) := by
    rw [P.shift_image_shift]
  constructor
  · rintro _ hx
    rw [← himage] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    have hmem := (E.shift_mem_rectVertices z 0 seed.radiusLeft
      (-(seed.radiusLeft : Real)) seed.radiusLeft u).2 ((seed.left i).1 hu)
    rw [hz0, hz1] at hmem
    simpa only [add_zero, sub_eq_add_neg, add_comm] using hmem
  · have ht := E.rectLeftConnection_translate_measureReal_eq mu hTI z
      0 seed.radiusLeft (-(seed.radiusLeft : Real)) seed.radiusLeft
      (P.shift base '' (S : Set V))
    rw [hz0, hz1, himage] at ht
    have hp := (seed.left i).2
    change p < mu.real (E.rectSideConnectionEvent 0 seed.radiusLeft
      (-(seed.radiusLeft : Real)) seed.radiusLeft
      (P.shift base '' (S : Set V))
      (E.rectLeftBoundaryVertices 0 seed.radiusLeft
        (-(seed.radiusLeft : Real)) seed.radiusLeft)) at hp
    rw [← ht] at hp
    simpa only [base, add_assoc, add_zero, sub_eq_add_neg, add_comm] using hp


theorem PeriodicPlaneEmbedding.NormalBoundaryBandSeed.right_tangential
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    {S : Finset V} {margin : Nat} {p : Real}
    (seed : E.NormalBoundaryBandSeed mu S margin p)
    (tangent : Fin (margin + 1) → Int) (i : Fin (margin + 1)) :
    let shift := seed.baseRight + horizontalShift (-(i.val : Int)) +
      verticalShift (tangent i)
    P.shift shift '' (S : Set V) ⊆
        E.rectVertices (-(seed.radiusRight : Real)) 0
          ((tangent i : Real) - seed.radiusRight)
          ((tangent i : Real) + seed.radiusRight) ∧
      p < mu.real (E.rectSideConnectionEvent
        (-(seed.radiusRight : Real)) 0
        ((tangent i : Real) - seed.radiusRight)
        ((tangent i : Real) + seed.radiusRight)
        (P.shift shift '' (S : Set V))
        (E.rectRightBoundaryVertices (-(seed.radiusRight : Real)) 0
          ((tangent i : Real) - seed.radiusRight)
          ((tangent i : Real) + seed.radiusRight))) := by
  dsimp only
  let base := seed.baseRight + horizontalShift (-(i.val : Int))
  let z := verticalShift (tangent i)
  have hz0 : (z 0 : Real) = 0 := by simp [z]
  have hz1 : (z 1 : Real) = tangent i := by simp [z]
  have himage : P.shift z '' (P.shift base '' (S : Set V)) =
      P.shift (base + verticalShift (tangent i)) '' (S : Set V) := by
    rw [P.shift_image_shift]
  constructor
  · rintro _ hx
    rw [← himage] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    have hmem := (E.shift_mem_rectVertices z (-(seed.radiusRight : Real)) 0
      (-(seed.radiusRight : Real)) seed.radiusRight u).2 ((seed.right i).1 hu)
    rw [hz0, hz1] at hmem
    simpa only [add_zero, sub_eq_add_neg, add_comm] using hmem
  · have ht := E.rectRightConnection_translate_measureReal_eq mu hTI z
      (-(seed.radiusRight : Real)) 0 (-(seed.radiusRight : Real))
      seed.radiusRight (P.shift base '' (S : Set V))
    rw [hz0, hz1, himage] at ht
    have hp := (seed.right i).2
    change p < mu.real (E.rectSideConnectionEvent
      (-(seed.radiusRight : Real)) 0 (-(seed.radiusRight : Real))
      seed.radiusRight (P.shift base '' (S : Set V))
      (E.rectRightBoundaryVertices (-(seed.radiusRight : Real)) 0
        (-(seed.radiusRight : Real)) seed.radiusRight)) at hp
    rw [← ht] at hp
    simpa only [base, add_assoc, add_zero, sub_eq_add_neg, add_comm] using hp


theorem PeriodicPlaneEmbedding.NormalBoundaryBandSeed.bottom_tangential
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    {S : Finset V} {margin : Nat} {p : Real}
    (seed : E.NormalBoundaryBandSeed mu S margin p)
    (tangent : Fin (margin + 1) → Int) (i : Fin (margin + 1)) :
    let shift := seed.baseBottom + verticalShift i.val +
      horizontalShift (tangent i)
    P.shift shift '' (S : Set V) ⊆
        E.rectVertices ((tangent i : Real) - seed.radiusBottom)
          ((tangent i : Real) + seed.radiusBottom) 0 seed.radiusBottom ∧
      p < mu.real (E.rectSideConnectionEvent
        ((tangent i : Real) - seed.radiusBottom)
        ((tangent i : Real) + seed.radiusBottom) 0 seed.radiusBottom
        (P.shift shift '' (S : Set V))
        (E.rectBottomBoundaryVertices
          ((tangent i : Real) - seed.radiusBottom)
          ((tangent i : Real) + seed.radiusBottom) 0 seed.radiusBottom)) := by
  dsimp only
  let base := seed.baseBottom + verticalShift i.val
  let z := horizontalShift (tangent i)
  have hz0 : (z 0 : Real) = tangent i := by simp [z]
  have hz1 : (z 1 : Real) = 0 := by simp [z]
  have himage : P.shift z '' (P.shift base '' (S : Set V)) =
      P.shift (base + horizontalShift (tangent i)) '' (S : Set V) := by
    rw [P.shift_image_shift]
  constructor
  · rintro _ hx
    rw [← himage] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    have hmem := (E.shift_mem_rectVertices z (-(seed.radiusBottom : Real))
      seed.radiusBottom 0 seed.radiusBottom u).2 ((seed.bottom i).1 hu)
    rw [hz0, hz1] at hmem
    simpa only [add_zero, sub_eq_add_neg, add_comm] using hmem
  · have ht := E.rectBottomConnection_translate_measureReal_eq mu hTI z
      (-(seed.radiusBottom : Real)) seed.radiusBottom 0 seed.radiusBottom
      (P.shift base '' (S : Set V))
    rw [hz0, hz1, himage] at ht
    have hp := (seed.bottom i).2
    rw [← ht] at hp
    simpa only [base, add_assoc, add_zero, sub_eq_add_neg, add_comm] using hp


theorem PeriodicPlaneEmbedding.NormalBoundaryBandSeed.top_tangential
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    {S : Finset V} {margin : Nat} {p : Real}
    (seed : E.NormalBoundaryBandSeed mu S margin p)
    (tangent : Fin (margin + 1) → Int) (i : Fin (margin + 1)) :
    let shift := seed.baseTop + verticalShift (-(i.val : Int)) +
      horizontalShift (tangent i)
    P.shift shift '' (S : Set V) ⊆
        E.rectVertices ((tangent i : Real) - seed.radiusTop)
          ((tangent i : Real) + seed.radiusTop)
          (-(seed.radiusTop : Real)) 0 ∧
      p < mu.real (E.rectSideConnectionEvent
        ((tangent i : Real) - seed.radiusTop)
        ((tangent i : Real) + seed.radiusTop)
        (-(seed.radiusTop : Real)) 0 (P.shift shift '' (S : Set V))
        (E.rectTopBoundaryVertices
          ((tangent i : Real) - seed.radiusTop)
          ((tangent i : Real) + seed.radiusTop)
          (-(seed.radiusTop : Real)) 0)) := by
  dsimp only
  let base := seed.baseTop + verticalShift (-(i.val : Int))
  let z := horizontalShift (tangent i)
  have hz0 : (z 0 : Real) = tangent i := by simp [z]
  have hz1 : (z 1 : Real) = 0 := by simp [z]
  have himage : P.shift z '' (P.shift base '' (S : Set V)) =
      P.shift (base + horizontalShift (tangent i)) '' (S : Set V) := by
    rw [P.shift_image_shift]
  constructor
  · rintro _ hx
    rw [← himage] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    have hmem := (E.shift_mem_rectVertices z (-(seed.radiusTop : Real))
      seed.radiusTop (-(seed.radiusTop : Real)) 0 u).2 ((seed.top i).1 hu)
    rw [hz0, hz1] at hmem
    simpa only [add_zero, sub_eq_add_neg, add_comm] using hmem
  · have ht := E.rectTopConnection_translate_measureReal_eq mu hTI z
      (-(seed.radiusTop : Real)) seed.radiusTop (-(seed.radiusTop : Real)) 0
      (P.shift base '' (S : Set V))
    rw [hz0, hz1, himage] at ht
    have hp := (seed.top i).2
    rw [← ht] at hp
    simpa only [base, add_assoc, add_zero, sub_eq_add_neg, add_comm] using hp


theorem PeriodicPlaneEmbedding.NormalBoundaryBandSeed.left_translate_to_rect
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    {S : Finset V} {margin : Nat} {p : Real}
    (seed : E.NormalBoundaryBandSeed mu S margin p)
    (i : Fin (margin + 1)) (z : Site 2) (b c d : Real)
    (hb : (seed.radiusLeft : Real) + z 0 ≤ b)
    (hc : c ≤ -(seed.radiusLeft : Real) + z 1)
    (hd : (seed.radiusLeft : Real) + z 1 ≤ d) :
    P.shift z ''
        (P.shift (seed.baseLeft + horizontalShift i.val) '' (S : Set V)) ⊆
          E.rectVertices (z 0) b c d ∧
      p < mu.real (E.rectSideConnectionEvent (z 0) b c d
        (P.shift z ''
          (P.shift (seed.baseLeft + horizontalShift i.val) '' (S : Set V)))
        (E.rectLeftBoundaryVertices (z 0) b c d)) := by
  let source := P.shift (seed.baseLeft + horizontalShift i.val) '' (S : Set V)
  constructor
  · rintro _ ⟨u, hu, rfl⟩
    have hmem := (E.shift_mem_rectVertices z 0 seed.radiusLeft
      (-(seed.radiusLeft : Real)) seed.radiusLeft u).2 ((seed.left i).1 hu)
    exact E.rectVertices_mono (by simp) hb hc hd hmem
  · have ht := E.rectLeftConnection_translate_measureReal_eq mu hTI z
      0 seed.radiusLeft (-(seed.radiusLeft : Real)) seed.radiusLeft source
    have hp := (seed.left i).2
    have hp' : p < mu.real (E.rectSideConnectionEvent (z 0)
        ((seed.radiusLeft : Real) + z 0)
        (-(seed.radiusLeft : Real) + z 1)
        ((seed.radiusLeft : Real) + z 1) (P.shift z '' source)
        (E.rectLeftBoundaryVertices (z 0)
          ((seed.radiusLeft : Real) + z 0)
          (-(seed.radiusLeft : Real) + z 1)
          ((seed.radiusLeft : Real) + z 1))) := by
      have hp0 : p < mu.real (E.rectSideConnectionEvent 0 seed.radiusLeft
          (-(seed.radiusLeft : Real)) seed.radiusLeft source
          (E.rectLeftBoundaryVertices 0 seed.radiusLeft
            (-(seed.radiusLeft : Real)) seed.radiusLeft)) := by
        simpa only [source] using hp
      simpa only [zero_add] using hp0.trans_eq ht.symm
    exact hp'.trans_le (measureReal_mono
      (E.rectLeftConnectionEvent_mono_otherBounds _ hb hc hd))


theorem PeriodicPlaneEmbedding.NormalBoundaryBandSeed.right_translate_to_rect
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    {S : Finset V} {margin : Nat} {p : Real}
    (seed : E.NormalBoundaryBandSeed mu S margin p)
    (i : Fin (margin + 1)) (z : Site 2) (a c d : Real)
    (ha : a ≤ -(seed.radiusRight : Real) + z 0)
    (hc : c ≤ -(seed.radiusRight : Real) + z 1)
    (hd : (seed.radiusRight : Real) + z 1 ≤ d) :
    P.shift z '' (P.shift
        (seed.baseRight + horizontalShift (-(i.val : Int))) '' (S : Set V)) ⊆
          E.rectVertices a (z 0) c d ∧
      p < mu.real (E.rectSideConnectionEvent a (z 0) c d
        (P.shift z '' (P.shift
          (seed.baseRight + horizontalShift (-(i.val : Int))) '' (S : Set V)))
        (E.rectRightBoundaryVertices a (z 0) c d)) := by
  let source := P.shift
    (seed.baseRight + horizontalShift (-(i.val : Int))) '' (S : Set V)
  constructor
  · rintro _ ⟨u, hu, rfl⟩
    have hmem := (E.shift_mem_rectVertices z (-(seed.radiusRight : Real)) 0
      (-(seed.radiusRight : Real)) seed.radiusRight u).2 ((seed.right i).1 hu)
    exact E.rectVertices_mono ha (by simp) hc hd hmem
  · have ht := E.rectRightConnection_translate_measureReal_eq mu hTI z
      (-(seed.radiusRight : Real)) 0
      (-(seed.radiusRight : Real)) seed.radiusRight source
    have hp := (seed.right i).2
    have hp' : p < mu.real (E.rectSideConnectionEvent
        (-(seed.radiusRight : Real) + z 0) (z 0)
        (-(seed.radiusRight : Real) + z 1)
        ((seed.radiusRight : Real) + z 1) (P.shift z '' source)
        (E.rectRightBoundaryVertices
          (-(seed.radiusRight : Real) + z 0) (z 0)
          (-(seed.radiusRight : Real) + z 1)
          ((seed.radiusRight : Real) + z 1))) := by
      have hp0 : p < mu.real (E.rectSideConnectionEvent
          (-(seed.radiusRight : Real)) 0 (-(seed.radiusRight : Real))
          seed.radiusRight source (E.rectRightBoundaryVertices
            (-(seed.radiusRight : Real)) 0 (-(seed.radiusRight : Real))
            seed.radiusRight)) := by
        simpa only [source] using hp
      simpa only [zero_add] using hp0.trans_eq ht.symm
    exact hp'.trans_le (measureReal_mono
      (E.rectRightConnectionEvent_mono_otherBounds _ ha hc hd))


theorem PeriodicPlaneEmbedding.NormalBoundaryBandSeed.bottom_translate_to_rect
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    {S : Finset V} {margin : Nat} {p : Real}
    (seed : E.NormalBoundaryBandSeed mu S margin p)
    (i : Fin (margin + 1)) (z : Site 2) (a b d : Real)
    (ha : a ≤ -(seed.radiusBottom : Real) + z 0)
    (hb : (seed.radiusBottom : Real) + z 0 ≤ b)
    (hd : (seed.radiusBottom : Real) + z 1 ≤ d) :
    P.shift z ''
        (P.shift (seed.baseBottom + verticalShift i.val) '' (S : Set V)) ⊆
          E.rectVertices a b (z 1) d ∧
      p < mu.real (E.rectSideConnectionEvent a b (z 1) d
        (P.shift z ''
          (P.shift (seed.baseBottom + verticalShift i.val) '' (S : Set V)))
        (E.rectBottomBoundaryVertices a b (z 1) d)) := by
  let source := P.shift (seed.baseBottom + verticalShift i.val) '' (S : Set V)
  constructor
  · rintro _ ⟨u, hu, rfl⟩
    have hmem := (E.shift_mem_rectVertices z (-(seed.radiusBottom : Real))
      seed.radiusBottom 0 seed.radiusBottom u).2 ((seed.bottom i).1 hu)
    exact E.rectVertices_mono ha hb (by simp) hd hmem
  · have ht := E.rectBottomConnection_translate_measureReal_eq mu hTI z
      (-(seed.radiusBottom : Real)) seed.radiusBottom 0 seed.radiusBottom source
    have hp := (seed.bottom i).2
    have hp' : p < mu.real (E.rectSideConnectionEvent
        (-(seed.radiusBottom : Real) + z 0)
        ((seed.radiusBottom : Real) + z 0) (z 1)
        ((seed.radiusBottom : Real) + z 1) (P.shift z '' source)
        (E.rectBottomBoundaryVertices
          (-(seed.radiusBottom : Real) + z 0)
          ((seed.radiusBottom : Real) + z 0) (z 1)
          ((seed.radiusBottom : Real) + z 1))) := by
      have hp0 : p < mu.real (E.rectSideConnectionEvent
          (-(seed.radiusBottom : Real)) seed.radiusBottom 0 seed.radiusBottom
          source (E.rectBottomBoundaryVertices
            (-(seed.radiusBottom : Real)) seed.radiusBottom 0
            seed.radiusBottom)) := by
        simpa only [source] using hp
      simpa only [zero_add] using hp0.trans_eq ht.symm
    exact hp'.trans_le (measureReal_mono
      (E.rectBottomConnectionEvent_mono_otherBounds _ ha hb hd))


theorem PeriodicPlaneEmbedding.NormalBoundaryBandSeed.top_translate_to_rect
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    {S : Finset V} {margin : Nat} {p : Real}
    (seed : E.NormalBoundaryBandSeed mu S margin p)
    (i : Fin (margin + 1)) (z : Site 2) (a b c : Real)
    (ha : a ≤ -(seed.radiusTop : Real) + z 0)
    (hb : (seed.radiusTop : Real) + z 0 ≤ b)
    (hc : c ≤ -(seed.radiusTop : Real) + z 1) :
    P.shift z '' (P.shift
        (seed.baseTop + verticalShift (-(i.val : Int))) '' (S : Set V)) ⊆
          E.rectVertices a b c (z 1) ∧
      p < mu.real (E.rectSideConnectionEvent a b c (z 1)
        (P.shift z '' (P.shift
          (seed.baseTop + verticalShift (-(i.val : Int))) '' (S : Set V)))
        (E.rectTopBoundaryVertices a b c (z 1))) := by
  let source := P.shift
    (seed.baseTop + verticalShift (-(i.val : Int))) '' (S : Set V)
  constructor
  · rintro _ ⟨u, hu, rfl⟩
    have hmem := (E.shift_mem_rectVertices z (-(seed.radiusTop : Real))
      seed.radiusTop (-(seed.radiusTop : Real)) 0 u).2 ((seed.top i).1 hu)
    exact E.rectVertices_mono ha hb hc (by simp) hmem
  · have ht := E.rectTopConnection_translate_measureReal_eq mu hTI z
      (-(seed.radiusTop : Real)) seed.radiusTop
      (-(seed.radiusTop : Real)) 0 source
    have hp := (seed.top i).2
    have hp' : p < mu.real (E.rectSideConnectionEvent
        (-(seed.radiusTop : Real) + z 0)
        ((seed.radiusTop : Real) + z 0)
        (-(seed.radiusTop : Real) + z 1) (z 1) (P.shift z '' source)
        (E.rectTopBoundaryVertices
          (-(seed.radiusTop : Real) + z 0)
          ((seed.radiusTop : Real) + z 0)
          (-(seed.radiusTop : Real) + z 1) (z 1))) := by
      have hp0 : p < mu.real (E.rectSideConnectionEvent
          (-(seed.radiusTop : Real)) seed.radiusTop
          (-(seed.radiusTop : Real)) 0 source
          (E.rectTopBoundaryVertices (-(seed.radiusTop : Real))
            seed.radiusTop (-(seed.radiusTop : Real)) 0)) := by
        simpa only [source] using hp
      simpa only [zero_add] using hp0.trans_eq ht.symm
    exact hp'.trans_le (measureReal_mono
      (E.rectTopConnectionEvent_mono_otherBounds _ ha hb hc))


theorem PeriodicPlaneEmbedding.exists_orbitBox_normalBoundaryBandSeed
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (N margin : Nat) {delta : Real} (hdelta : 0 < delta) :
    Nonempty (E.NormalBoundaryBandSeed mu (P.orbitBox N) margin
      ((mu.real (P.setHitsInfinite (P.orbitBox N : Set V))) ^ 2 - delta)) := by
  classical
  obtain ⟨baseLeft, hbaseLeft⟩ :=
    E.exists_shift_orbitBox_subset_rightHalfPlane N 0
  obtain ⟨baseRight, hbaseRight⟩ :=
    E.exists_shift_orbitBox_subset_leftComplement N 0
  obtain ⟨baseBottomSwap, hbaseBottom⟩ :=
    E.axisSwap.exists_shift_orbitBox_subset_rightHalfPlane N 0
  obtain ⟨baseTopSwap, hbaseTop⟩ :=
    E.axisSwap.exists_shift_orbitBox_subset_leftComplement N 0
  let baseBottom := siteAxisSwap baseBottomSwap
  let baseTop := siteAxisSwap baseTopSwap
  have hinsideLeft (i : Fin (margin + 1)) :
      P.shift (baseLeft + horizontalShift i.val) ''
          (P.orbitBox N : Set V) ⊆ E.rightHalfPlaneVertices 0 := by
    rintro _ ⟨u, hu, rfl⟩
    have h := hbaseLeft u hu
    change 0 ≤ E.vertexCoord (P.shift baseLeft u) 0 at h
    simp only [E.vertexCoord_shift] at h
    change 0 ≤ E.vertexCoord
      (P.shift (baseLeft + horizontalShift i.val) u) 0
    simp only [P.shift_add, E.vertexCoord_shift]
    simpa using add_nonneg h (show (0 : Real) ≤ i.val by positivity)
  have hinsideRight (i : Fin (margin + 1)) :
      P.shift (baseRight + horizontalShift (-(i.val : Int))) ''
          (P.orbitBox N : Set V) ⊆ {u | E.vertexCoord u 0 ≤ 0} := by
    rintro _ ⟨u, hu, rfl⟩
    have h := hbaseRight u hu
    change ¬ (0 ≤ E.vertexCoord (P.shift baseRight u) 0) at h
    simp only [E.vertexCoord_shift] at h
    change E.vertexCoord
      (P.shift (baseRight + horizontalShift (-(i.val : Int))) u) 0 ≤ 0
    simp only [P.shift_add, E.vertexCoord_shift]
    have hi : (0 : Real) ≤ i.val := by positivity
    simp only [horizontalShift_zero_apply, Int.cast_neg, Int.cast_natCast]
    linarith
  have hinsideBottom (i : Fin (margin + 1)) :
      P.shift (baseBottom + verticalShift i.val) ''
          (P.orbitBox N : Set V) ⊆ {u | 0 ≤ E.vertexCoord u 1} := by
    rintro _ ⟨u, hu, rfl⟩
    have h := hbaseBottom u (by rw [P.axisSwap_orbitBox]; exact hu)
    change 0 ≤ E.axisSwap.vertexCoord
      (P.axisSwap.shift baseBottomSwap u) 0 at h
    have h' : 0 ≤ E.vertexCoord (P.shift baseBottom u) 1 := by
      simpa [baseBottom, PeriodicGraph.axisSwap] using h
    simp only [E.vertexCoord_shift] at h'
    change 0 ≤ E.vertexCoord
      (P.shift (baseBottom + verticalShift i.val) u) 1
    simp only [P.shift_add, E.vertexCoord_shift]
    simpa using add_nonneg h' (show (0 : Real) ≤ i.val by positivity)
  have hinsideTop (i : Fin (margin + 1)) :
      P.shift (baseTop + verticalShift (-(i.val : Int))) ''
          (P.orbitBox N : Set V) ⊆ {u | E.vertexCoord u 1 ≤ 0} := by
    rintro _ ⟨u, hu, rfl⟩
    have h := hbaseTop u (by rw [P.axisSwap_orbitBox]; exact hu)
    change ¬ (0 ≤ E.axisSwap.vertexCoord
      (P.axisSwap.shift baseTopSwap u) 0) at h
    have h' : ¬ (0 ≤ E.vertexCoord (P.shift baseTop u) 1) := by
      simpa [baseTop, PeriodicGraph.axisSwap] using h
    simp only [E.vertexCoord_shift] at h'
    change E.vertexCoord
      (P.shift (baseTop + verticalShift (-(i.val : Int))) u) 1 ≤ 0
    simp only [P.shift_add, E.vertexCoord_shift]
    have hi : (0 : Real) ≤ i.val := by positivity
    simp only [verticalShift_one_apply, Int.cast_neg, Int.cast_natCast]
    linarith
  obtain ⟨radiusLeft, hleft⟩ :=
    E.exists_translatedFamily_leftBoundaryExhaustion_measureReal_gt
      mu hFKG hTI hunique 0 (P.orbitBox N)
      (fun i : Fin (margin + 1) => baseLeft + horizontalShift i.val)
      hinsideLeft hdelta
  obtain ⟨radiusRight, hright⟩ :=
    E.exists_translatedFamily_rightBoundaryExhaustion_measureReal_gt
      mu hFKG hTI hunique 0 (P.orbitBox N)
      (fun i : Fin (margin + 1) =>
        baseRight + horizontalShift (-(i.val : Int)))
      (by simpa only [neg_zero] using hinsideRight) hdelta
  obtain ⟨radiusBottom, hbottom⟩ :=
    E.exists_translatedFamily_bottomBoundaryExhaustion_measureReal_gt
      mu hFKG hTI hunique 0 (P.orbitBox N)
      (fun i : Fin (margin + 1) => baseBottom + verticalShift i.val)
      hinsideBottom hdelta
  obtain ⟨radiusTop, htop⟩ :=
    E.exists_translatedFamily_topBoundaryExhaustion_measureReal_gt
      mu hFKG hTI hunique 0 (P.orbitBox N)
      (fun i : Fin (margin + 1) =>
        baseTop + verticalShift (-(i.val : Int)))
      (by simpa only [neg_zero] using hinsideTop) hdelta
  exact ⟨{
    baseLeft := baseLeft
    baseRight := baseRight
    baseBottom := baseBottom
    baseTop := baseTop
    radiusLeft := radiusLeft
    radiusRight := radiusRight
    radiusBottom := radiusBottom
    radiusTop := radiusTop
    left := by
      simpa [PeriodicPlaneEmbedding.leftBoundaryExhaustionVertices,
        PeriodicPlaneEmbedding.leftBoundaryExhaustionEvent] using hleft
    right := by simpa using hright
    bottom := by simpa using hbottom
    top := by simpa using htop }⟩


end StatMech.FK.PeriodicPlanar
