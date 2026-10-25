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
import Def.StatisticalMechanics.Code.FK.EdgeConfigZ.Part5
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


section EdgeFreeEnergy

variable {d : ℕ}


theorem ecz_ivp2_eq_edgeFE (t : ℝ) (n : ℕ) (hE : 0 < (boxGraph d n).edgeFinset.card) :
    ivp2_tiltFreeEnergy (boxGraph d n) 2 t
      = (ecz_NE (boxGraph d n) : ℝ) / ((boxGraph d n).edgeFinset.card : ℝ) * Real.log 2
        + ecz_edgeFreeEnergy d t n := by
  unfold ivp2_tiltFreeEnergy ecz_edgeFreeEnergy ecz_u
  set p := fsc_logistic t
  have hp0 : (0:ℝ) < p := fsc_logistic_pos t
  have hp1 : p < 1 := fsc_logistic_lt_one t
  have hfact : fkZ (boxGraph d n) p 2 = 2 ^ ecz_NE (boxGraph d n) * ecz_fkZEdge (boxGraph d n) p 2 :=
    ecz_factorization (boxGraph d n) p 2
  have hZE : 0 < ecz_fkZEdge (boxGraph d n) p 2 := ecz_fkZEdge_pos _ hp0 hp1 (by norm_num)
  have h2 : (0:ℝ) < (2:ℝ) ^ ecz_NE (boxGraph d n) := by positivity
  rw [hfact, Real.log_mul h2.ne' hZE.ne', Real.log_pow]
  have hEne : ((boxGraph d n).edgeFinset.card : ℝ) ≠ 0 := by exact_mod_cast hE.ne'
  field_simp
  ring


theorem ecz_centered_eq_cfe (t : ℝ) (n : ℕ) (hE : 0 < (boxGraph d n).edgeFinset.card) :
    cfe_centered (boxGraph d n) 2 t = ecz_edgeFreeEnergy d t n - ecz_edgeFreeEnergy d 0 n := by
  unfold cfe_centered
  rw [ecz_ivp2_eq_edgeFE t n hE, ecz_ivp2_eq_edgeFE 0 n hE]
  ring


theorem ecz_edgeFE_eq (t : ℝ) (n : ℕ) :
    ecz_edgeFreeEnergy d t n = -(ecz_u d t n / agl_E d n) + Real.log (1 + Real.exp t) := by
  rfl

end EdgeFreeEnergy
end FK
end StatMech
