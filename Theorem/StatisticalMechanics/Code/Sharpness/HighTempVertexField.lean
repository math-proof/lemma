/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempVertexField.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.HighTempSimon.Part8
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
import Def.StatisticalMechanics.Code.Sharpness.HighTempVertexField
open Finset SimpleGraph
open scoped BigOperators Classical

set_option maxHeartbeats 1600000


namespace StatMech

namespace Sharpness

open Ising

open FieldGhostDict

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


@[simp] theorem vertexGhostCoupling_some_some
    (J : Sym2 V → ℝ) (H : V → ℝ) (x y : V) :
    vertexGhostCoupling J H s(some x, some y) = J s(x, y) := rfl

@[simp] theorem vertexGhostCoupling_some_none
    (J : Sym2 V → ℝ) (H : V → ℝ) (x : V) :
    vertexGhostCoupling J H s(some x, none) = H x := rfl


end Sharpness
end StatMech
