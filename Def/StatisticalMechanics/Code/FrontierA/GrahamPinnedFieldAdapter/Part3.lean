/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedFieldAdapter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamHeadlineAdapter
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamGraphAdapter
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamPinnedVBGTriangle
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamPinnedFieldAdapter.Part2
open Finset SimpleGraph
open scoped BigOperators
open Classical


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Sharpness StatMech.ConfigSpace

open StatMech.Walls.VBG

variable {V : Type*} [Fintype V] [DecidableEq V]


def grahamAnchorSlice (m : V) (b : Bool)
    (eta : {x : V // x ≠ m} -> Bool) : ConfigSpace V :=
  (Equiv.funSplitAt m Bool).symm (b, eta)

end StatMech.FrontierA
