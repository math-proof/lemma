/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorDiagonal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianFourColorFamilies.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianFourColorDiagonal.Part2
open Finset
open Classical

set_option linter.unusedSectionVars false


namespace StatMech.FrontierA

open StatMech.Sharpness.RandomCurrent

variable {ι V : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype V] [DecidableEq V]


def FiniteTreeDiagonalBranchInequality
    (ends : ι -> Sym2 V) (U : Finset ι) (i j k l : V) : Prop :=
  #(finiteTreeDiagonalColorings ends U i j k l) ≤
    ∑ y : V, #(finiteTreeSeparatedBranchColorings ends U i j k l y)


end StatMech.FrontierA
