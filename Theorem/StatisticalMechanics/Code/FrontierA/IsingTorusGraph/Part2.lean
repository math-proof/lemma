module
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusStationarity
public import Theorem.StatisticalMechanics.Code.Sharpness.HighTempSimon.Part8
public import Theorem.StatisticalMechanics.Code.Sharpness.HighTempPlusBox.Part5
public import Instance.StatisticalMechanics.Code.FrontierA.IsingTorusGraph
open Finset
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusGraph.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech.Ising StatMech.Sharpness

variable {d k : Nat}

@[simp] theorem isingTorusGraph_adj_iff
    (x y : IsingDyadicTorus d k) :
    (isingTorusGraph d k).Adj x y ↔ ∃ i : Fin d,
      y = x + isingTorusStep i ∨ x = y + isingTorusStep i := Iff.rfl


end StatMech.FrontierA
