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
public import Def.StatisticalMechanics.Code.Walls.rbtbutterfly
open Finset
open scoped BigOperators

public section

namespace StatMech.Walls.Reimer

set_option linter.style.longLine false


@[simp] lemma rbt_inner2_eq (u v : Bool → ℝ) :
    rbt_inner2 u v = u false * v false + u true * v true := by
  simp only [rbt_inner2, Fintype.sum_bool]; ring


lemma rbt_inner2_e_f (c : Bool) : rbt_inner2 (rbt_e2 c) (rbt_f2 (!c)) = 0 := by
  cases c <;> simp [rbt_e2, rbt_f2]


lemma rbt_inner2_e_g (c : Bool) : rbt_inner2 (rbt_e2 c) (rbt_g2 (!c) (!c)) = 0 := by
  cases c <;> simp [rbt_e2, rbt_g2]


lemma rbt_inner2_f_g (c : Bool) : rbt_inner2 (rbt_f2 c) (rbt_g2 (!c) c) = 0 := by
  cases c <;> simp [rbt_f2, rbt_g2]


end StatMech.Walls.Reimer
