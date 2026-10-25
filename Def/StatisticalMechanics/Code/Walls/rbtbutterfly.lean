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
import Abbrev.StatisticalMechanics.Code.Walls.rbtbutterfly
open Finset
open scoped BigOperators


namespace StatMech.Walls.Reimer

set_option linter.style.longLine false


def rbt_e2 (c : Bool) : Bool → ℝ :=
  fun z => if c = false then (1 : ℝ) else (if z = false then 0 else 1)


def rbt_f2 (c : Bool) : Bool → ℝ :=
  fun z => if c = false then (if z = false then 1 else 0) else (if z = false then 1 else -1)


def rbt_g2 (c d : Bool) : Bool → ℝ :=
  fun z =>
    match c, d with
    | false, false => if z = false then 1 else 0     
    | false, true  => 1                              
    | true,  false => if z = false then 0 else 1     
    | true,  true  => if z = false then 1 else -1    


def rbt_inner2 (u v : Bool → ℝ) : ℝ := ∑ z : Bool, u z * v z

end StatMech.Walls.Reimer
