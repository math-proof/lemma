/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.TwoDim.ZhangBKData.Part6
import Theorem.StatisticalMechanics.Code.Universality.FrameChangeIso.Part8
import Theorem.StatisticalMechanics.Code.Universality.CrossingReflection.Part4
import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part101
import Theorem.StatisticalMechanics.Code.Universality.KestenBXPWire
import Def.StatisticalMechanics.Code.TwoDim.ZhangFixedK.Part6
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal


namespace StatMech.TwoDim

open StatMech.Lattice StatMech.Universality StatMech.Percolation

open StatMech.RSW.Box


theorem zfk_leftSquare_subset_matched (N : ℕ) :
    zfk_leftSquare N ⊆ zfk_matchedRect N := by
  intro z hz
  simp only [zfk_leftSquare, zfk_matchedRect, mem_rect] at hz ⊢
  omega

theorem zfk_rightSquare_subset_matched (N : ℕ) :
    zfk_rightSquare N ⊆ zfk_matchedRect N := by
  intro z hz
  simp only [zfk_rightSquare, zfk_matchedRect, mem_rect] at hz ⊢
  omega

theorem zfk_box_subset_matched (N : ℕ) :
    box 2 N ⊆ zfk_matchedRect N := by
  intro z hz
  rw [zfk_matchedRect, mem_rect]
  have hz' := (zbd_mem_box_iff_rect N z).mp hz
  rw [mem_rect] at hz'
  omega


theorem zfk_mergedArmPair_subset_horizontalCrossing (k N : ℕ) :
    zfk_MergedArmPairEvent k N ⊆
      StatMech.RSW.Box.horizontalCrossingEvent (-(N : ℤ)) ((N : ℤ) + 1)
        (-(N : ℤ)) (N : ℤ) := by
  intro omega h
  obtain ⟨x, _hxK, y, _hyK, _hxInf, _hyInf, hxArm, hyArm, hxy⟩ := h
  obtain ⟨hxL, a, hax⟩ := hxArm
  obtain ⟨hyR, b, hyb⟩ := hyArm
  obtain ⟨hxB, hyB, hxyB⟩ := hxy
  have hax' : ConnectedWithin 2 omega (zfk_matchedRect N)
      ⟨(a : Site 2), zfk_leftSquare_subset_matched N
        (StatMech.RSW.Box.leftSide_subset a.2)⟩
      ⟨x, zfk_leftSquare_subset_matched N hxL⟩ :=
    StatMech.RSW.Strip.connectedWithin_mono_set omega
      (zfk_leftSquare_subset_matched N) hax
  have hxy' : ConnectedWithin 2 omega (zfk_matchedRect N)
      ⟨x, zfk_box_subset_matched N hxB⟩
      ⟨y, zfk_box_subset_matched N hyB⟩ :=
    StatMech.RSW.Strip.connectedWithin_mono_set omega
      (zfk_box_subset_matched N) hxyB
  have hyb' : ConnectedWithin 2 omega (zfk_matchedRect N)
      ⟨y, zfk_rightSquare_subset_matched N hyR⟩
      ⟨(b : Site 2), zfk_rightSquare_subset_matched N
        (StatMech.RSW.Box.rightSide_subset b.2)⟩ :=
    StatMech.RSW.Strip.connectedWithin_mono_set omega
      (zfk_rightSquare_subset_matched N) hyb
  let a' : StatMech.RSW.Box.leftSide
      (-(N : ℤ)) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ) :=
    ⟨a, zfk_leftSquare_subset_matched N
      (StatMech.RSW.Box.leftSide_subset a.2), a.2.2⟩
  let b' : StatMech.RSW.Box.rightSide
      (-(N : ℤ)) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ) :=
    ⟨b, zfk_rightSquare_subset_matched N
      (StatMech.RSW.Box.rightSide_subset b.2), b.2.2⟩
  refine ⟨a', b', ?_⟩
  exact hax'.trans (hxy'.trans hyb')


end StatMech.TwoDim
