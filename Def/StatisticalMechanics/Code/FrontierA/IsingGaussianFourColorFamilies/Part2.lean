/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorFamilies.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianFourColorSwitch.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedBridge.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianFourColorFamilies
open Finset
open Classical


namespace StatMech.FrontierA

open StatMech.Sharpness.RandomCurrent

open StatMech.GrahamGHS.FourColor

variable {ι V : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype V] [DecidableEq V]


noncomputable def finiteTreeMixedColorings
    (ends : ι -> Sym2 V) (U : Finset ι) (i j k l : V) :
    Finset (GrahamFourColoring ι) :=
  (grahamFourColorings U).filter (fun q =>
    sources ends q.color1 = {i, j} ∧
      sources ends q.color2 = {k, l} ∧
      sources ends q.color3 = ∅ ∧
      sources ends (q.color4 U) = ∅ ∧
      connK ends (q.color1 ∪ q.color2) i k)


noncomputable def finiteTreeSeparatedBranchColorings
    (ends : ι -> Sym2 V) (U : Finset ι) (i j k l y : V) :
    Finset (GrahamFourColoring ι) :=
  (grahamFourColorings U).filter (fun q =>
    sources ends q.color1 = {i, j} ∧
      sources ends q.color2 = ∅ ∧
      sources ends q.color3 = {k, l} ∧
      sources ends (q.color4 U) = ∅ ∧
      connK ends (q.color1 ∪ q.color2) i y ∧
      connK ends (q.color3 ∪ q.color4 U) k y)

end StatMech.FrontierA
