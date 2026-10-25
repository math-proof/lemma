/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fkc_rqbdd.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.EdgeConfigZ.Part15
import Theorem.StatisticalMechanics.Code.FK.SecantClose.Part3
import Def.StatisticalMechanics.Code.Walls.fkc_rqbdd
open scoped BigOperators
open SimpleGraph Filter Topology Set

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 1000000


namespace StatMech.Walls

open StatMech StatMech.FK StatMech.Lattice


section FreeEnergy

theorem fkc_edgeFreeEnergy_eq_ecz (d : ℕ) (s : ℝ) (n : ℕ) :
    fkc_edgeFreeEnergy d s 2 n = ecz_edgeFreeEnergy d s n := by
  unfold fkc_edgeFreeEnergy ecz_edgeFreeEnergy ecz_u
  rw [neg_div, neg_neg]


theorem fkc_rq_bdd (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) (s q : ℝ) (hq1 : 1 ≤ q) :
    fkc_edgeFreeEnergy d s q n ≤ (Real.log 2 + 2 * Real.log q) + Real.log (1 + Real.exp s) := by
  unfold fkc_edgeFreeEnergy
  set E := (boxGraph d n).edgeFinset.card with hEdef
  set Vc := Fintype.card (boxVerts d n) with hVdef
  set p := fsc_logistic s with hpdef
  have hp0 : (0:ℝ) < p := fsc_logistic_pos s
  have hp1 : p < 1 := fsc_logistic_lt_one s
  have hE : 0 < E := ecz_box_edge_pos d hd hn
  have hEr : (0:ℝ) < (E:ℝ) := by exact_mod_cast hE
  have hZpos : 0 < ecz_fkZEdge (boxGraph d n) p q :=
    ecz_fkZEdge_pos _ hp0 hp1 (by linarith)
  have hub : ecz_fkZEdge (boxGraph d n) p q ≤ (2:ℝ)^E * q^Vc :=
    fkc_fkZEdge_le _ hp0 hp1 hq1
  have hlogq : (0:ℝ) ≤ Real.log q := Real.log_nonneg hq1
  have hlog2 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog : Real.log (ecz_fkZEdge (boxGraph d n) p q) ≤ (E:ℝ) * Real.log 2 + (Vc:ℝ) * Real.log q := by
    calc Real.log (ecz_fkZEdge (boxGraph d n) p q)
        ≤ Real.log ((2:ℝ)^E * q^Vc) := Real.log_le_log hZpos hub
      _ = (E:ℝ) * Real.log 2 + (Vc:ℝ) * Real.log q := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  have hVle : (Vc:ℝ) ≤ 2 * E := by exact_mod_cast ecz_boxVerts_le_edges d n hd hn
  have hkey : Real.log (ecz_fkZEdge (boxGraph d n) p q) / (E:ℝ)
      ≤ Real.log 2 + 2 * Real.log q := by
    rw [div_le_iff₀ hEr]
    calc Real.log (ecz_fkZEdge (boxGraph d n) p q)
        ≤ (E:ℝ) * Real.log 2 + (Vc:ℝ) * Real.log q := hlog
      _ ≤ (E:ℝ) * Real.log 2 + (2 * E) * Real.log q := by
          have : (Vc:ℝ) * Real.log q ≤ (2 * E) * Real.log q :=
            mul_le_mul_of_nonneg_right hVle hlogq
          linarith
      _ = (Real.log 2 + 2 * Real.log q) * E := by ring
  linarith

end FreeEnergy
end StatMech.Walls
