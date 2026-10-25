/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/SelfDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
import Def.StatisticalMechanics.Code.RSW.SelfDuality
open SimpleGraph Real


namespace StatMech

namespace RSW

open StatMech.Lattice


theorem selfDualPoint_mem_Ioo {q : ℝ} (hq : 0 < q) :
    selfDualPoint q ∈ Set.Ioo (0 : ℝ) 1 := by
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have h1s : (0 : ℝ) < 1 + Real.sqrt q := by linarith
  refine ⟨?_, ?_⟩
  · rw [selfDualPoint]; positivity
  · rw [selfDualPoint, div_lt_one h1s]; linarith

theorem selfDualPoint_pos {q : ℝ} (hq : 0 < q) : 0 < selfDualPoint q :=
  (selfDualPoint_mem_Ioo hq).1

theorem selfDualPoint_lt_one {q : ℝ} (hq : 0 < q) : selfDualPoint q < 1 :=
  (selfDualPoint_mem_Ioo hq).2


theorem dualParam_selfDualPoint {q : ℝ} (hq : 0 < q) :
    dualParam (selfDualPoint q) q (selfDualPoint q) := by
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have hsq : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq.le
  set s := Real.sqrt q with hsdef
  have h1s : (0 : ℝ) < 1 + s := by linarith
  have hp : selfDualPoint q = s / (1 + s) := rfl
  rw [dualParam, hp]
  have h1p : 1 - s / (1 + s) = 1 / (1 + s) := by field_simp; ring
  rw [h1p, div_mul_div_comm, div_mul_div_comm, div_div_div_cancel_right₀]
  · rw [mul_one]; nlinarith [hsq]
  · positivity


theorem dualParam_self_iff {q : ℝ} (hq : 0 < q) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    dualParam p q p ↔ p = selfDualPoint q := by
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have hsq : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq.le
  have h1p : (0 : ℝ) < 1 - p := by linarith
  set s := Real.sqrt q with hsdef
  have h1s : (0 : ℝ) < 1 + s := by linarith
  rw [dualParam, selfDualPoint, ← hsdef]
  constructor
  · intro h
    have hmul : p * p = q * ((1 - p) * (1 - p)) := by field_simp at h; linarith [h]
    
    have hpe : p = s * (1 - p) := by
      have hpos : 0 < s * (1 - p) := mul_pos hs h1p
      nlinarith [hmul, hsq, hp0, hpos, mul_pos hp0 hp0]
    field_simp
    nlinarith [hpe]
  · intro h; subst h
    have h1pe : 1 - s / (1 + s) = 1 / (1 + s) := by field_simp; ring
    rw [div_mul_div_comm, h1pe, div_mul_div_comm, div_div_div_cancel_right₀]
    · rw [mul_one]; nlinarith [hsq]
    · positivity


end RSW
end StatMech
