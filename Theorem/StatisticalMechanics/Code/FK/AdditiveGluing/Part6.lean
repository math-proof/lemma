/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/AdditiveGluing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.FKInterfaceSubadd.Part2
import Theorem.StatisticalMechanics.Code.FK.SuperMultiplicative.Part4
import Theorem.StatisticalMechanics.Code.FK.BoxFeketePerVolume.Part2
import Theorem.StatisticalMechanics.Code.FK.BoxTiling.Part2
import Theorem.StatisticalMechanics.Code.FK.GenuineEdgeCollapse
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Def.StatisticalMechanics.Code.FK.AdditiveGluing.Part6
open scoped BigOperators
open SimpleGraph Filter Topology Set MeasureTheory

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option maxHeartbeats 1000000


namespace StatMech

namespace FK

open StatMech.Lattice


variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]


@[simp] theorem agl_K_zero : agl_K 0 = 1 := rfl

theorem agl_K_succ (j : ℕ) : agl_K (j + 1) = 2 * agl_K j + 1 := by
  unfold agl_K
  have h1 : 1 ≤ 2 ^ (j + 1) := Nat.one_le_two_pow
  have h2 : 1 ≤ 2 ^ (j + 1 + 1) := Nat.one_le_two_pow
  omega

theorem agl_K_pos (j : ℕ) : 1 ≤ agl_K j := by
  unfold agl_K
  have : 2 ≤ 2 ^ (j + 1) := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem agl_K_tendsto_atTop : Tendsto agl_K atTop atTop := by
  apply tendsto_atTop_atTop.mpr
  intro b
  refine ⟨b, fun j hj => ?_⟩
  unfold agl_K
  have h1 : b + 1 ≤ 2 ^ (j + 1) := by
    calc b + 1 ≤ j + 1 := by omega
      _ ≤ 2 ^ (j + 1) := Nat.lt_two_pow_self.le
  omega


end FK
end StatMech
