module
public import Theorem.StatisticalMechanics.Code.Sharpness.ABClusterCondition
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Def.StatisticalMechanics.Code.Sharpness.ABCouplingReindex
open Finset SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABCouplingReindex.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


@[simp] theorem abcrEndpointSum_mk (F : V → ℝ) (x y : V) :
    abcrEndpointSum F s(x, y) = F x + F y := rfl


end Sharpness
end StatMech
