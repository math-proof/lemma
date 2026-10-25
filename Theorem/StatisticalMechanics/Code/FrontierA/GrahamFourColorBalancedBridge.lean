/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part17
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamLemmaOneFourColor
import Def.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedBridge
open Finset
open Classical


namespace StatMech.FrontierA

open StatMech.Sharpness.RandomCurrent

open StatMech.GrahamGHS.FourColor

variable {ι W : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype W] [DecidableEq W]


theorem mem_balanced_colorClass_iff
    (U : Finset ι) (c : ↑U -> Fin 4) (a : Fin 4) (i : ι) :
    i ∈ colorClass U c a ↔ ∃ hi : i ∈ U, c ⟨i, hi⟩ = a := by
  simp [colorClass]

theorem colorClass_grahamToBalancedColor_zero
    (U : Finset ι) (q : GrahamFourColoring ι)
    (hq : q.IsPartition U) :
    colorClass U (grahamToBalancedColor U q) 0 = q.color1 := by
  ext i
  rw [mem_balanced_colorClass_iff]
  constructor
  · rintro ⟨hi, hx⟩
    by_cases h1 : i ∈ q.color1 <;>
      by_cases h2 : i ∈ q.color2 <;>
      by_cases h3 : i ∈ q.color3 <;>
      simp [grahamToBalancedColor, h1, h2, h3] at hx ⊢
  · intro hi
    refine ⟨hq.1 hi, ?_⟩
    simp [grahamToBalancedColor, hi]

theorem colorClass_grahamToBalancedColor_one
    (U : Finset ι) (q : GrahamFourColoring ι)
    (hq : q.IsPartition U) :
    colorClass U (grahamToBalancedColor U q) 1 = q.color2 := by
  ext i
  rw [mem_balanced_colorClass_iff]
  constructor
  · rintro ⟨hiU, hx⟩
    by_cases h1 : i ∈ q.color1 <;>
      by_cases h2 : i ∈ q.color2 <;>
      by_cases h3 : i ∈ q.color3 <;>
      simp [grahamToBalancedColor, h1, h2, h3] at hx ⊢
  · intro hi
    have hiU := hq.2.1 hi
    have hi1 : i ∉ q.color1 := by
      intro hi1
      exact Finset.disjoint_left.mp hq.2.2.2.1 hi1 hi
    refine ⟨hiU, ?_⟩
    simp [grahamToBalancedColor, hi1, hi]

theorem colorClass_grahamToBalancedColor_two
    (U : Finset ι) (q : GrahamFourColoring ι)
    (hq : q.IsPartition U) :
    colorClass U (grahamToBalancedColor U q) 2 = q.color3 := by
  ext i
  rw [mem_balanced_colorClass_iff]
  constructor
  · rintro ⟨hiU, hx⟩
    by_cases h1 : i ∈ q.color1 <;>
      by_cases h2 : i ∈ q.color2 <;>
      by_cases h3 : i ∈ q.color3 <;>
      simp [grahamToBalancedColor, h1, h2, h3] at hx ⊢
  · intro hi
    have hiU := hq.2.2.1 hi
    have hi1 : i ∉ q.color1 := by
      intro hi1
      exact Finset.disjoint_left.mp hq.2.2.2.2.1 hi1 hi
    have hi2 : i ∉ q.color2 := by
      intro hi2
      exact Finset.disjoint_left.mp hq.2.2.2.2.2 hi2 hi
    refine ⟨hiU, ?_⟩
    simp [grahamToBalancedColor, hi1, hi2, hi]

theorem colorClass_grahamToBalancedColor_three
    (U : Finset ι) (q : GrahamFourColoring ι)
    (hq : q.IsPartition U) :
    colorClass U (grahamToBalancedColor U q) 3 = q.color4 U := by
  ext i
  rw [mem_balanced_colorClass_iff]
  simp only [GrahamFourColoring.color4, Finset.mem_sdiff,
    Finset.mem_union]
  constructor
  · rintro ⟨hiU, hx⟩
    by_cases h1 : i ∈ q.color1 <;>
      by_cases h2 : i ∈ q.color2 <;>
      by_cases h3 : i ∈ q.color3 <;>
      simp [grahamToBalancedColor, h1, h2, h3] at hx ⊢
    exact hiU
  · rintro ⟨hiU, hi⟩
    simp only [not_or] at hi
    refine ⟨hiU, ?_⟩
    simp [grahamToBalancedColor, hi.1.1, hi.1.2, hi.2]


theorem grahamToBalancedColor_leftPattern
    (ends : ι -> Sym2 W) (U : Finset ι) (j k l m : W)
    (q : GrahamFourColoring ι)
    (hq : q ∈ grahamLemmaOneSeparatedColorings ends U j k l m) :
    LeftPattern ends U {j, k} {k, l} k m
      (grahamToBalancedColor U q) := by
  rw [mem_grahamLemmaOneSeparatedColorings] at hq
  rcases hq with ⟨hpart, h1, h2, h3, h4, hd1, hd2⟩
  unfold LeftPattern RowsDisconnect
  rw [colorClass_grahamToBalancedColor_zero U q hpart,
    colorClass_grahamToBalancedColor_one U q hpart,
    colorClass_grahamToBalancedColor_two U q hpart,
    colorClass_grahamToBalancedColor_three U q hpart,
    rowClass_zero, rowClass_one,
    colorClass_grahamToBalancedColor_zero U q hpart,
    colorClass_grahamToBalancedColor_one U q hpart,
    colorClass_grahamToBalancedColor_two U q hpart,
    colorClass_grahamToBalancedColor_three U q hpart]
  exact ⟨h1, h2, h3, h4, hd1, hd2⟩


end StatMech.FrontierA
