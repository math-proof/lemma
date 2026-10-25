/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWContent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Universality.HexBridgeDecomp.Part9
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeWeight.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralCountLaws.Part3
import Def.StatisticalMechanics.Code.Universality.HexW2Cut.Part5
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWContent.Part2


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


theorem hhc_plusHalf_ne_minusHalf : hhc_plusHalf ≠ hhc_minusHalf := by
  intro h
  have hv : ([hhc_plusBridge] : List HexBridge) = [hhc_minusBridge] :=
    congrArg Subtype.val h
  have hb : hhc_plusBridge = hhc_minusBridge := by simpa using hv
  have hc := congrArg HexBridge.content hb
  simp [hhc_plusBridge, hhc_minusBridge] at hc


theorem hhc_width_projection_not_injective :
    ¬ Function.Injective hhc_widths := by
  intro hinj
  apply hhc_plusHalf_ne_minusHalf
  apply hinj
  simp [hhc_widths, hbw_widthFinset, hhc_plusHalf, hhc_minusHalf,
    hhc_plusBridge, hhc_minusBridge]


theorem hhc_sum_grouped_by_widths (S : Finset HexHWContentHalf)
    (w : HexHWContentHalf → ℝ) :
    ∑ s ∈ S, w s =
      ∑ widths ∈ S.image hhc_widths,
        ∑ s ∈ S with hhc_widths s = widths, w s := by
  classical
  symm
  exact Finset.sum_fiberwise_of_maps_to
    (fun s hs => Finset.mem_image_of_mem hhc_widths hs) w


end StatMech.Universality
