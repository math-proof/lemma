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
import Def.StatisticalMechanics.Code.FK.IVPressureConvex
open MeasureTheory Set Filter Topology Real Finset
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice


variable {ι : Type*} [Fintype ι]


theorem ivp2_Ssum_pos (w a : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hpos : ∃ i, 0 < w i) (t : ℝ) :
    0 < ivp2_Ssum w a t :=
  Finset.sum_pos' (fun i _ => mul_nonneg (hw i) (Real.exp_pos _).le)
    (by obtain ⟨j, hj⟩ := hpos; exact ⟨j, Finset.mem_univ j, mul_pos hj (Real.exp_pos _)⟩)


theorem ivp2_Ssum_hasDerivAt (w a : ι → ℝ) (t : ℝ) :
    HasDerivAt (ivp2_Ssum w a) (ivp2_S1 w a t) t :=
  ivp2_sumExp_hasDerivAt w a t


theorem ivp2_S1_hasDerivAt (w a : ι → ℝ) (t : ℝ) :
    HasDerivAt (ivp2_S1 w a) (ivp2_S2 w a t) t := by
  have h := ivp2_sumExp_hasDerivAt (fun i => w i * a i) a t
  have hfun : (fun s => ∑ i, (fun i => w i * a i) i * Real.exp (a i * s)) = ivp2_S1 w a := by
    funext s; rfl
  have hval : (∑ i, (fun i => w i * a i) i * a i * Real.exp (a i * t)) = ivp2_S2 w a t := by
    unfold ivp2_S2; apply Finset.sum_congr rfl; intro i _; ring
  rw [hfun, hval] at h; exact h


theorem ivp2_cauchy_schwarz_cgf (w a : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (t : ℝ) :
    (ivp2_S1 w a t) ^ 2 ≤ (ivp2_S2 w a t) * (ivp2_Ssum w a t) := by
  unfold ivp2_S1 ivp2_S2 ivp2_Ssum
  set f : ι → ℝ := fun i => Real.sqrt (w i * Real.exp (a i * t)) * a i with hf
  set g : ι → ℝ := fun i => Real.sqrt (w i * Real.exp (a i * t)) with hg
  have hcs := sum_mul_sq_le_sq_mul_sq Finset.univ f g
  have e1 : (∑ i, f i * g i) = ∑ i, w i * a i * Real.exp (a i * t) := by
    apply Finset.sum_congr rfl; intro i _; simp only [hf, hg]
    rw [mul_right_comm, Real.mul_self_sqrt (mul_nonneg (hw i) (Real.exp_pos _).le)]; ring
  have e2 : (∑ i, f i ^ 2) = ∑ i, w i * a i ^ 2 * Real.exp (a i * t) := by
    apply Finset.sum_congr rfl; intro i _; simp only [hf]
    rw [mul_pow, Real.sq_sqrt (mul_nonneg (hw i) (Real.exp_pos _).le)]; ring
  have e3 : (∑ i, g i ^ 2) = ∑ i, w i * Real.exp (a i * t) := by
    apply Finset.sum_congr rfl; intro i _; simp only [hg]
    rw [Real.sq_sqrt (mul_nonneg (hw i) (Real.exp_pos _).le)]
  rw [e1, e2, e3] at hcs; exact hcs


end FK
end StatMech
