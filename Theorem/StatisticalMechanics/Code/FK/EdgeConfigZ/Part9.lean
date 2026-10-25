/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.SuperMultiplicative.Part4
import Theorem.StatisticalMechanics.Code.FK.FKInterfaceSubadd.Part2
import Theorem.StatisticalMechanics.Code.FK.QuadrantPartition.Part9
import Theorem.StatisticalMechanics.Code.FK.CenteredFreeEnergy.Part3
import Theorem.StatisticalMechanics.Code.FK.BoxFeketePerVolume.Part2
import Def.StatisticalMechanics.Code.FK.EdgeConfigZ.Part10
open scoped BigOperators
open SimpleGraph Filter Topology Set

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000


namespace StatMech

namespace FK

open StatMech.Lattice


section BoxNesting

variable {d : ℕ}


section VanHove

variable {d : ℕ}


theorem ecz_center_mem_box (m n : ℕ) (c : Fin d → Fin (ecz_T m n)) (y : Site d)
    (hy : y ∈ box d m) : (fun i => y i + ecz_center m n c i) ∈ box d n := by
  rw [mem_box]
  intro i
  rw [qp_natAbs_iff]
  have hyi : -(m : ℤ) ≤ y i ∧ y i ≤ m := (qp_natAbs_iff (y i) m).mp (hy i)
  have hci : (c i : ℕ) < ecz_T m n := (c i).2
  have hcT : ((c i : ℤ)) * (2 * m + 1) + (2 * m + 1) ≤ 2 * n + 1 := by
    have h1 : ((c i : ℕ) + 1) * (2 * m + 1) ≤ ecz_T m n * (2 * m + 1) := by
      apply Nat.mul_le_mul_right; omega
    have h2 : ecz_T m n * (2 * m + 1) ≤ 2 * n + 1 := ecz_T_mul_le m n
    have h3 : ((c i : ℕ) + 1) * (2 * m + 1) ≤ 2 * n + 1 := le_trans h1 h2
    have : (((c i : ℕ) + 1) * (2 * m + 1) : ℤ) ≤ ((2 * n + 1 : ℕ) : ℤ) := by exact_mod_cast h3
    push_cast at this ⊢; nlinarith [this]
  have hc0 : (0 : ℤ) ≤ (c i : ℤ) := Int.ofNat_nonneg _
  simp only [ecz_center]
  constructor
  · nlinarith [hyi.1, hc0]
  · nlinarith [hyi.2, hcT]


end VanHove
end BoxNesting
end FK
end StatMech
