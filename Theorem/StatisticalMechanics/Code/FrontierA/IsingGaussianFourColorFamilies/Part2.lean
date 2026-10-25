/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorFamilies.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianFourColorSwitch.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedBridge.Part2
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianFourColorFamilies.Part2
open Finset
open Classical


namespace StatMech.FrontierA

open StatMech.Sharpness.RandomCurrent

open StatMech.GrahamGHS.FourColor

variable {ι V : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype V] [DecidableEq V]


@[simp] theorem mem_finiteTreeMixedColorings
    (ends : ι -> Sym2 V) (U : Finset ι) (i j k l : V)
    (q : GrahamFourColoring ι) :
    q ∈ finiteTreeMixedColorings ends U i j k l ↔
      q.IsPartition U ∧
      sources ends q.color1 = {i, j} ∧
      sources ends q.color2 = {k, l} ∧
      sources ends q.color3 = ∅ ∧
      sources ends (q.color4 U) = ∅ ∧
      connK ends (q.color1 ∪ q.color2) i k := by
  simp [finiteTreeMixedColorings]

@[simp] theorem mem_finiteTreeSeparatedBranchColorings
    (ends : ι -> Sym2 V) (U : Finset ι) (i j k l y : V)
    (q : GrahamFourColoring ι) :
    q ∈ finiteTreeSeparatedBranchColorings ends U i j k l y ↔
      q.IsPartition U ∧
      sources ends q.color1 = {i, j} ∧
      sources ends q.color2 = ∅ ∧
      sources ends q.color3 = {k, l} ∧
      sources ends (q.color4 U) = ∅ ∧
      connK ends (q.color1 ∪ q.color2) i y ∧
      connK ends (q.color3 ∪ q.color4 U) k y := by
  simp [finiteTreeSeparatedBranchColorings]


theorem finiteTreeMixedPattern_grahamToBalancedColor_iff
    (ends : ι -> Sym2 V) (U : Finset ι) (i j k l : V)
    (q : GrahamFourColoring ι) (hq : q.IsPartition U) :
    FiniteTreeMixedPattern ends U i j k l
        (grahamToBalancedColor U q) ↔
      sources ends q.color1 = {i, j} ∧
      sources ends q.color2 = {k, l} ∧
      sources ends q.color3 = ∅ ∧
      sources ends (q.color4 U) = ∅ ∧
      connK ends (q.color1 ∪ q.color2) i k := by
  unfold FiniteTreeMixedPattern
  rw [colorClass_grahamToBalancedColor_zero U q hq,
    colorClass_grahamToBalancedColor_one U q hq,
    colorClass_grahamToBalancedColor_two U q hq,
    colorClass_grahamToBalancedColor_three U q hq]


theorem finiteTreeSeparatedBranchPattern_grahamToBalancedColor_iff
    (ends : ι -> Sym2 V) (U : Finset ι) (i j k l y : V)
    (q : GrahamFourColoring ι) (hq : q.IsPartition U) :
    FiniteTreeSeparatedBranchPattern ends U i j k l y
        (grahamToBalancedColor U q) ↔
      sources ends q.color1 = {i, j} ∧
      sources ends q.color2 = ∅ ∧
      sources ends q.color3 = {k, l} ∧
      sources ends (q.color4 U) = ∅ ∧
      connK ends (q.color1 ∪ q.color2) i y ∧
      connK ends (q.color3 ∪ q.color4 U) k y := by
  unfold FiniteTreeSeparatedBranchPattern FiniteTreeSeparatedSources
  rw [colorClass_grahamToBalancedColor_zero U q hq,
    colorClass_grahamToBalancedColor_one U q hq,
    colorClass_grahamToBalancedColor_two U q hq,
    colorClass_grahamToBalancedColor_three U q hq]
  tauto


theorem finiteTreeMixedColorings_card_le_sum_of_injective
    (ends : ι -> Sym2 V) (U : Finset ι) (i j k l : V)
    (f : (↥(finiteTreeMixedColorings ends U i j k l)) ->
      Σ y : V, ↥(finiteTreeSeparatedBranchColorings ends U i j k l y))
    (hf : Function.Injective f) :
    #(finiteTreeMixedColorings ends U i j k l) ≤
      ∑ y : V, #(finiteTreeSeparatedBranchColorings ends U i j k l y) := by
  have h := Fintype.card_le_of_injective f hf
  rw [Fintype.card_sigma] at h
  simpa only [Fintype.card_coe] using h

end StatMech.FrontierA
