/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rbtbutterfly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Order.WellFoundedSet
import Theorem.StatisticalMechanics.Code.Walls.rbtbutterfly
open Finset
open scoped BigOperators


namespace StatMech.Walls.Reimer

set_option linter.style.longLine false


def rbt_tens {m : ℕ} (v : Fin m → Bool → ℝ) : rbt_Q m → ℝ :=
  fun z => ∏ i, v i (z i)


def rbt_e {m : ℕ} (x : rbt_Q m) : rbt_Q m → ℝ := rbt_tens (fun i => rbt_e2 (x i))


def rbt_f {m : ℕ} (x : rbt_Q m) : rbt_Q m → ℝ := rbt_tens (fun i => rbt_f2 (x i))


def rbt_g {m : ℕ} (x y : rbt_Q m) : rbt_Q m → ℝ := rbt_tens (fun i => rbt_g2 (x i) (y i))


def rbt_inner {m : ℕ} (A B : rbt_Q m → ℝ) : ℝ := ∑ z : rbt_Q m, A z * B z


end StatMech.Walls.Reimer
