module
public import Theorem.StatisticalMechanics.Code.Universality.HexContentChoiceBound
public import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWContent.Part12
public import Def.StatisticalMechanics.Code.Universality.HexHWBridgeSubsetBound.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexHWBridgeSubsetBound.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open scoped BigOperators


theorem hhs_bridgeEncoding_injective
    (S : Finset HexHWContentHalf) :
    Set.InjOn (hhs_bridgeEncoding S) (S : Set HexHWContentHalf) := by
  classical
  intro s hs t ht heq
  apply Subtype.ext
  apply strictDecreasingWidths_eq_of_mem_iff s.2 t.2
  intro b
  constructor
  · intro hb
    have hactive := hhs_mem_activeBridges hs hb
    have hv := congrFun (congrFun heq b) hactive
    change decide (b ∈ s.1) = decide (b ∈ t.1) at hv
    have hsbool : decide (b ∈ s.1) = true := by simp [hb]
    have htbool : decide (b ∈ t.1) = true := by
      rw [← hv]
      exact hsbool
    exact of_decide_eq_true htbool
  · intro hb
    have hactive := hhs_mem_activeBridges ht hb
    have hv := congrFun (congrFun heq b) hactive
    change decide (b ∈ s.1) = decide (b ∈ t.1) at hv
    have htbool : decide (b ∈ t.1) = true := by simp [hb]
    have hsbool : decide (b ∈ s.1) = true := by
      rw [hv]
      exact htbool
    exact of_decide_eq_true hsbool

end StatMech.Universality
