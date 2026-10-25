/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamLemmaOneFourColor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.Switching.Part3
import Def.StatisticalMechanics.Code.FrontierA.GrahamLemmaOneFourColor
open Finset SimpleGraph
open scoped symmDiff
open Classical


namespace StatMech.FrontierA

open StatMech.Sharpness.RandomCurrent

variable {ι W : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype W] [DecidableEq W]


@[simp] theorem mem_grahamFourColorings
    (U : Finset ι) (c : GrahamFourColoring ι) :
    c ∈ grahamFourColorings U ↔ c.IsPartition U := by
  simp [grahamFourColorings]

@[simp] theorem mem_grahamLemmaOneMixedColorings
    (ends : ι -> Sym2 W) (U : Finset ι) (j k l m : W)
    (c : GrahamFourColoring ι) :
    c ∈ grahamLemmaOneMixedColorings ends U j k l m ↔
      c.IsPartition U ∧
      sources ends c.color1 = {j, k} ∧
      sources ends c.color2 = {k, l} ∧
      sources ends c.color3 = ∅ ∧
      sources ends (c.color4 U) = ∅ ∧
      ¬ connK ends (c.color1 ∪ c.color2) k m := by
  simp [grahamLemmaOneMixedColorings]

@[simp] theorem mem_grahamLemmaOneSeparatedColorings
    (ends : ι -> Sym2 W) (U : Finset ι) (j k l m : W)
    (c : GrahamFourColoring ι) :
    c ∈ grahamLemmaOneSeparatedColorings ends U j k l m ↔
      c.IsPartition U ∧
      sources ends c.color1 = {j, k} ∧
      sources ends c.color2 = ∅ ∧
      sources ends c.color3 = {k, l} ∧
      sources ends (c.color4 U) = ∅ ∧
      ¬ connK ends (c.color1 ∪ c.color2) k m ∧
      ¬ connK ends (c.color3 ∪ c.color4 U) k m := by
  simp [grahamLemmaOneSeparatedColorings]

end StatMech.FrontierA
