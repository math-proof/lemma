/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorSwitch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part17
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCorrections.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianFourColorSwitch.Part4
open Finset
open scoped symmDiff
open Classical


namespace StatMech.FrontierA

open StatMech.Sharpness.RandomCurrent

open StatMech.GrahamGHS.FourColor

variable {ι V : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype V] [DecidableEq V]


noncomputable def finiteTreeInvariantComponentTransfer
    (ends : ι -> Sym2 V) (U : Finset ι) (k : V)
    (c : ↑U -> Fin 4) : Finset ι :=
  edgeComponent ends (finiteTreeMiddleUnion U c) k

end StatMech.FrontierA
