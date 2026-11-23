/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rbtbutterfly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Order.WellFoundedSet
public import Theorem.StatisticalMechanics.Code.Walls.rbtbutterfly.Part2

@[expose] public section

open Finset
open scoped BigOperators


namespace StatMech.Walls.Reimer

set_option linter.style.longLine false


def rbt_antipode {m : ℕ} (x : rbt_Q m) : rbt_Q m := fun i => !(x i)


def rbt_inCube {m : ℕ} (y z x : rbt_Q m) : Prop := ∀ i, x i = y i ∨ x i = z i


def rbt_inRed {m : ℕ} (y z x : rbt_Q m) : Prop := rbt_inCube y z x


def rbt_inYellow {m : ℕ} (y z x : rbt_Q m) : Prop := rbt_inCube y (rbt_antipode z) x


end StatMech.Walls.Reimer
