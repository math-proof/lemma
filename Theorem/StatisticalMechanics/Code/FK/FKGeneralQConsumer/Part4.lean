/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.fkc_rqvanhove.Part4
import Theorem.StatisticalMechanics.Code.FK.FKUniqPerEdge.Part3
import Theorem.StatisticalMechanics.Code.FK.FreeWeakLimit.Part8
import Theorem.StatisticalMechanics.Code.FK.MonotoneWeakLimit.Part2
import Def.StatisticalMechanics.Code.FK.FKGeneralQConsumer.Part3
open scoped BigOperators
open MeasureTheory Filter Topology SimpleGraph Set

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 2000000


namespace StatMech.FK

open StatMech.Lattice StatMech.IsingFK ConfigSpace

variable {d : ℕ}


theorem fkgq_unitMarg_tendsto (q : ℝ) (hq : 1 ≤ q) (dir : Fin d × Bool) (t : ℝ) :
    Tendsto (fun n => fkgq_unitMarg d q n dir t) atTop
      (nhds (freeEdgeDensity d q
        (edgeIncl d 1 (ocs_unitEdge d 1 (le_refl 1) dir)) (fsc_logistic t))) := by
  have hbase := fkgq_free_density_eq_limit (d := d) 1
    (ocs_unitEdge d 1 (le_refl 1) dir) (fsc_logistic_pos t) (fsc_logistic_lt_one t) hq
  have hmap : Tendsto (fun n : ℕ => Nat.sqrt n - 1) atTop atTop := by
    apply Filter.tendsto_atTop_atTop.mpr
    intro b
    refine ⟨(b + 1) * (b + 1), fun n hn => ?_⟩
    have : b + 1 ≤ Nat.sqrt n := by
      calc b + 1 = Nat.sqrt ((b + 1) * (b + 1)) := (Nat.sqrt_eq (b + 1)).symm
        _ ≤ Nat.sqrt n := Nat.sqrt_le_sqrt hn
    omega
  refine (hbase.comp hmap).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hR : 1 ≤ Nat.sqrt n := by rw [Nat.one_le_iff_ne_zero, Ne, Nat.sqrt_eq_zero]; omega
  simp only [Function.comp_apply, fkgq_unitMarg, dif_pos hR]
  rw [ocs_unitEdge_eq_innerEdgeLE d (Nat.sqrt n) hR dir]
  have hrr : 1 + (Nat.sqrt n - 1) = Nat.sqrt n := Nat.add_sub_cancel' hR
  exact congrArg (fun z : {z : ℕ // 1 ≤ z} =>
    edgeMargProb (fkProb (boxGraph d z.1) (fsc_logistic t) q)
      (innerEdgeLE d z.2 (ocs_unitEdge d 1 (le_refl 1) dir)))
    (show (⟨1 + (Nat.sqrt n - 1), Nat.le_add_right 1 _⟩ : {z : ℕ // 1 ≤ z})
        = ⟨Nat.sqrt n, hR⟩ from Subtype.ext hrr)


theorem fkgq_unitWiredMarg_tendsto (q : ℝ) (hq : 1 ≤ q) (dir : Fin d × Bool) (t : ℝ) :
    Tendsto (fun n => fkgq_unitWiredMarg d q n dir t) atTop
      (nhds (wiredEdgeDensity d q
        (edgeIncl d 1 (ocs_unitEdge d 1 (le_refl 1) dir)) (fsc_logistic t))) := by
  have hbase := fkgq_wired_density_eq_limit (d := d) 1
    (ocs_unitEdge d 1 (le_refl 1) dir) (fsc_logistic_pos t) (fsc_logistic_lt_one t) hq
  have hmap : Tendsto (fun n : ℕ => Nat.sqrt n - 1) atTop atTop := by
    apply Filter.tendsto_atTop_atTop.mpr
    intro b
    refine ⟨(b + 1) * (b + 1), fun n hn => ?_⟩
    have : b + 1 ≤ Nat.sqrt n := by
      calc b + 1 = Nat.sqrt ((b + 1) * (b + 1)) := (Nat.sqrt_eq (b + 1)).symm
        _ ≤ Nat.sqrt n := Nat.sqrt_le_sqrt hn
    omega
  refine (hbase.comp hmap).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hR : 1 ≤ Nat.sqrt n := by rw [Nat.one_le_iff_ne_zero, Ne, Nat.sqrt_eq_zero]; omega
  simp only [Function.comp_apply, fkgq_unitWiredMarg, dif_pos hR]
  rw [ocs_unitEdge_eq_innerEdgeLE d (Nat.sqrt n) hR dir]
  have hrr : 1 + (Nat.sqrt n - 1) = Nat.sqrt n := Nat.add_sub_cancel' hR
  exact congrArg (fun z : {z : ℕ // 1 ≤ z} =>
    edgeMargProb (wiredFkProb (boxGraph d z.1) (boxBoundary d z.1) (fsc_logistic t) q)
      (innerEdgeLE d z.2 (ocs_unitEdge d 1 (le_refl 1) dir)))
    (show (⟨1 + (Nat.sqrt n - 1), Nat.le_add_right 1 _⟩ : {z : ℕ // 1 ≤ z})
        = ⟨Nat.sqrt n, hR⟩ from Subtype.ext hrr)


end StatMech.FK
