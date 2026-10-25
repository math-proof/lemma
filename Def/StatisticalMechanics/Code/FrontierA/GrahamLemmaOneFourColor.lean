/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamLemmaOneFourColor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.Switching.Part3
import Structure.StatisticalMechanics.Code.FrontierA.GrahamLemmaOneFourColor
open Finset SimpleGraph
open scoped symmDiff
open Classical


namespace StatMech.FrontierA

open StatMech.Sharpness.RandomCurrent

variable {ι W : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype W] [DecidableEq W]


def GrahamFourColoring.color4 (U : Finset ι)
    (c : GrahamFourColoring ι) : Finset ι :=
  U \ (c.color1 ∪ c.color2 ∪ c.color3)


def GrahamFourColoring.IsPartition (U : Finset ι)
    (c : GrahamFourColoring ι) : Prop :=
  c.color1 ⊆ U ∧ c.color2 ⊆ U ∧ c.color3 ⊆ U ∧
    Disjoint c.color1 c.color2 ∧ Disjoint c.color1 c.color3 ∧
      Disjoint c.color2 c.color3


noncomputable def grahamFourColorings
    (U : Finset ι) : Finset (GrahamFourColoring ι) :=
  Finset.univ.filter (GrahamFourColoring.IsPartition U)


noncomputable def grahamLemmaOneMixedColorings
    (ends : ι -> Sym2 W) (U : Finset ι) (j k l m : W) :
    Finset (GrahamFourColoring ι) :=
  (grahamFourColorings U).filter (fun c =>
    sources ends c.color1 = {j, k} ∧
      sources ends c.color2 = {k, l} ∧
      sources ends c.color3 = ∅ ∧
      sources ends (c.color4 U) = ∅ ∧
      ¬ connK ends (c.color1 ∪ c.color2) k m)


noncomputable def grahamLemmaOneSeparatedColorings
    (ends : ι -> Sym2 W) (U : Finset ι) (j k l m : W) :
    Finset (GrahamFourColoring ι) :=
  (grahamFourColorings U).filter (fun c =>
    sources ends c.color1 = {j, k} ∧
      sources ends c.color2 = ∅ ∧
      sources ends c.color3 = {k, l} ∧
      sources ends (c.color4 U) = ∅ ∧
      ¬ connK ends (c.color1 ∪ c.color2) k m ∧
      ¬ connK ends (c.color3 ∪ c.color4 U) k m)

end StatMech.FrontierA
