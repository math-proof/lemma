/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorSwitch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part17
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCorrections.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianFourColorSwitch.Part2
open Finset
open scoped symmDiff
open Classical


namespace StatMech.FrontierA

open StatMech.Sharpness.RandomCurrent

open StatMech.GrahamGHS.FourColor

variable {ι V : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype V] [DecidableEq V]


def FiniteTreeMixedPattern
    (ends : ι -> Sym2 V) (U : Finset ι) (i j k l : V)
    (c : ↑U -> Fin 4) : Prop :=
  sources ends (colorClass U c 0) = {i, j} ∧
    sources ends (colorClass U c 1) = {k, l} ∧
    sources ends (colorClass U c 2) = ∅ ∧
    sources ends (colorClass U c 3) = ∅ ∧
    connK ends (colorClass U c 0 ∪ colorClass U c 1) i k


def FiniteTreeSeparatedSources
    (ends : ι -> Sym2 V) (U : Finset ι) (i j k l : V)
    (c : ↑U -> Fin 4) : Prop :=
  sources ends (colorClass U c 0) = {i, j} ∧
    sources ends (colorClass U c 1) = ∅ ∧
    sources ends (colorClass U c 2) = {k, l} ∧
    sources ends (colorClass U c 3) = ∅


end StatMech.FrontierA
