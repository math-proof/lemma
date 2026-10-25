/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IVPressureConvex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.Tilt.Part3
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.SecantClose.Part3
import Def.StatisticalMechanics.Code.FK.IVPressureConvex.Part4
open MeasureTheory Set Filter Topology Real Finset
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice


variable {ι : Type*} [Fintype ι]


variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem ivp2_softplus_convexOn : ConvexOn ℝ univ ivp2_softplus := by
  have hconv : ConvexOn ℝ univ (ivp2_Kcgf (fun _ : Bool => (1:ℝ)) (fun b => if b then 1 else 0)) :=
    ivp2_Kcgf_convexOn _ _ (fun _ => zero_le_one) ⟨false, one_pos⟩
  have heq : ivp2_softplus
      = ivp2_Kcgf (fun _ : Bool => (1:ℝ)) (fun b => if b then 1 else 0) := by
    funext t
    unfold ivp2_softplus ivp2_Kcgf ivp2_Ssum
    congr 1
    rw [Fintype.sum_bool]
    simp [add_comm]
  rw [heq]; exact hconv

end FK
end StatMech
