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
public import Def.StatisticalMechanics.Code.Walls.rbtbutterfly.Part2
open Finset
open scoped BigOperators

public section

namespace StatMech.Walls.Reimer

set_option linter.style.longLine false


theorem rbt_tens_inner {m : ℕ} (u v : Fin m → Bool → ℝ) :
    rbt_inner (rbt_tens u) (rbt_tens v) = ∏ i, rbt_inner2 (u i) (v i) := by
  simp only [rbt_inner, rbt_tens, rbt_inner2]
  
  rw [Fintype.prod_sum (fun i (z : Bool) => u i z * v i z)]
  
  apply Finset.sum_congr rfl
  intro z _
  rw [← Finset.prod_mul_distrib]


theorem rbt_e_perp_f {m : ℕ} (x y : rbt_Q m) (hxy : x ≠ y) :
    rbt_inner (rbt_e x) (rbt_f y) = 0 := by
  rw [rbt_e, rbt_f, rbt_tens_inner]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  have : y i = !(x i) := by cases hxy' : x i <;> cases hyi : y i <;> simp_all
  rw [this]; exact rbt_inner2_e_f (x i)


end StatMech.Walls.Reimer
