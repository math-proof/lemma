module
public import Theorem.StatisticalMechanics.Code.FrontierA.GrahamHeadlineAdapter
public import Theorem.StatisticalMechanics.Code.FrontierA.GrahamGraphAdapter
public import Theorem.StatisticalMechanics.Code.FrontierA.GrahamPinnedVBGTriangle
public import Theorem.StatisticalMechanics.Code.FrontierA.GrahamPinnedFieldAdapter
open Finset SimpleGraph
open scoped BigOperators
open Classical


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedFieldAdapter.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech.Ising StatMech.Sharpness StatMech.ConfigSpace

open StatMech.Walls.VBG

variable {V : Type*} [Fintype V] [DecidableEq V]


def grahamPinConfig (m : V) (t : ConfigSpace V) : ConfigSpace V :=
  Function.update t m true

end StatMech.FrontierA
