/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CylinderDecayClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.IntegralDecayClose.Part5
import Theorem.StatisticalMechanics.Code.FK.FiniteVolumeShift.Part5
import Theorem.StatisticalMechanics.Code.FK.CylinderDecayClose.Part5
open MeasureTheory Filter Topology BoundedContinuousFunction SimpleGraph Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators


namespace StatMech

namespace FK

open StatMech.IsingFK

variable {d : ℕ}


variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]


noncomputable def cdc_wiredDecaySet {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : Multiplicative (Site d)) (φ : ℕ → ℕ) :
    Submodule ℝ C(ConfigSpace (Sym2 (Site d)), ℝ) where
  carrier := {h | Tendsto (isd_decayFun
      (fun n => wiredFiniteMeasure d (φ n) hp hp1 (by norm_num : (0:ℝ) < 2)) g
      (BoundedContinuousFunction.mkOfCompact h)) atTop (𝓝 0)}
  add_mem' {h h'} hh hh' := by
    simp only [Set.mem_setOf_eq] at hh hh' ⊢
    have hsum := hh.add hh'
    rw [add_zero] at hsum
    refine hsum.congr (fun n => ?_)
    rw [BoundedContinuousFunction.mkOfCompact_add, cdc_decayFun_add]
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    have hz : isd_decayFun
        (fun n => wiredFiniteMeasure d (φ n) hp hp1 (by norm_num : (0:ℝ) < 2)) g
        (BoundedContinuousFunction.mkOfCompact (0 : C(ConfigSpace (Sym2 (Site d)), ℝ)))
      = fun _ => (0:ℝ) := by
      funext n
      rw [BoundedContinuousFunction.mkOfCompact_zero, cdc_decayFun_zero]
    rw [hz]; exact tendsto_const_nhds
  smul_mem' c h hh := by
    simp only [Set.mem_setOf_eq] at hh ⊢
    have hsmul := hh.const_mul c
    rw [mul_zero] at hsmul
    refine hsmul.congr (fun n => ?_)
    have hms : BoundedContinuousFunction.mkOfCompact (c • h)
        = c • BoundedContinuousFunction.mkOfCompact h := rfl
    rw [hms, cdc_decayFun_smul]


noncomputable def cdc_freeDecaySet {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : Multiplicative (Site d)) (φ : ℕ → ℕ) :
    Submodule ℝ C(ConfigSpace (Sym2 (Site d)), ℝ) where
  carrier := {h | Tendsto (isd_decayFun
      (fun n => freeFiniteMeasure d (φ n) hp hp1 (by norm_num : (0:ℝ) < 2)) g
      (BoundedContinuousFunction.mkOfCompact h)) atTop (𝓝 0)}
  add_mem' {h h'} hh hh' := by
    simp only [Set.mem_setOf_eq] at hh hh' ⊢
    have hsum := hh.add hh'
    rw [add_zero] at hsum
    refine hsum.congr (fun n => ?_)
    rw [BoundedContinuousFunction.mkOfCompact_add, cdc_decayFun_add]
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    have hz : isd_decayFun
        (fun n => freeFiniteMeasure d (φ n) hp hp1 (by norm_num : (0:ℝ) < 2)) g
        (BoundedContinuousFunction.mkOfCompact (0 : C(ConfigSpace (Sym2 (Site d)), ℝ)))
      = fun _ => (0:ℝ) := by
      funext n
      rw [BoundedContinuousFunction.mkOfCompact_zero, cdc_decayFun_zero]
    rw [hz]; exact tendsto_const_nhds
  smul_mem' c h hh := by
    simp only [Set.mem_setOf_eq] at hh ⊢
    have hsmul := hh.const_mul c
    rw [mul_zero] at hsmul
    refine hsmul.congr (fun n => ?_)
    have hms : BoundedContinuousFunction.mkOfCompact (c • h)
        = c • BoundedContinuousFunction.mkOfCompact h := rfl
    rw [hms, cdc_decayFun_smul]


end FK
end StatMech
