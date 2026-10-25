/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomVertexPartition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.GHSVertexPartition.Part8
import Def.StatisticalMechanics.Code.Ising.GHSInhomVertexPartition
open Finset Classical

set_option maxHeartbeats 1600000


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FieldGhostDict

variable {V : Type*} [Fintype V] [DecidableEq V]


@[simp] theorem ghsiGhostCoupling_some_some (K : Sym2 V → ℝ) (hf : V → ℝ)
    (x y : V) :
    ghsiGhostCoupling K hf s(some x, some y) = 2 * K s(x, y) := rfl

@[simp] theorem ghsiGhostCoupling_some_none (K : Sym2 V → ℝ) (hf : V → ℝ)
    (x : V) :
    ghsiGhostCoupling K hf s(some x, none) = 2 * hf x := rfl


end StatMech.Ising
