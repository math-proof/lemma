/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorSwitch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part17
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCorrections.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianFourColorSwitch
open Finset
open scoped symmDiff
open Classical


namespace StatMech.FrontierA

open StatMech.Sharpness.RandomCurrent

open StatMech.GrahamGHS.FourColor

variable {ι V : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype V] [DecidableEq V]


def finiteTreeMiddleUnion (U : Finset ι) (c : ↑U -> Fin 4) : Finset ι :=
  colorClass U c 1 ∪ colorClass U c 2


def FiniteTreeMiddleTransferWitness
    (ends : ι -> Sym2 V) (U : Finset ι) (k l : V)
    (c : ↑U -> Fin 4) (X : Finset ι) : Prop :=
  X ⊆ finiteTreeMiddleUnion U c ∧ sources ends X = {k, l} ∧
    connK ends X k l


noncomputable def finiteTreeMiddleTransferFromUnion
    (ends : ι -> Sym2 V) (M : Finset ι) (k l : V) : Finset ι :=
  if h : ∃ X, X ⊆ M ∧ sources ends X = {k, l} ∧ connK ends X k l then
    Classical.choose h
  else ∅


noncomputable def finiteTreeMiddleTransfer
    (ends : ι -> Sym2 V) (U : Finset ι) (k l : V)
    (c : ↑U -> Fin 4) : Finset ι :=
  finiteTreeMiddleTransferFromUnion ends (finiteTreeMiddleUnion U c) k l

end StatMech.FrontierA
