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
import Def.StatisticalMechanics.Code.FK.AdditiveGluing.Part8
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


variable (d : ℕ)


theorem agl_boxTiltFreeEnergy_tendsto (t : ℝ)
    (hbox : ∀ j, 0 < (boxGraph d (agl_K j)).edgeFinset.card)
    (hdoubling : agl_AdditiveDoublingBound d t)
    (hbdd : ∃ M : ℝ, ∀ j, |agl_u d t (agl_K j) / agl_E d (agl_K j)| ≤ M)
    (bj : ℕ → ℕ) (hbj : Tendsto bj atTop atTop)
    (osc : ℕ → ℝ) (hosc : Tendsto osc atTop (𝓝 0))
    (hsand : ∀ n, |ivp2_tiltFreeEnergy (boxGraph d n) 2 t
        - ivp2_tiltFreeEnergy (boxGraph d (agl_K (bj n))) 2 t| ≤ osc (bj n)) :
    ∃ L : ℝ, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 L) := by
  classical
  obtain ⟨I, hInn, hIsum, hudbl, hEdge⟩ := hdoubling
  obtain ⟨M, hM⟩ := hbdd
  set c : ℝ := -Real.log (1 - fsc_logistic t) with hc
  have hp1 : fsc_logistic t < 1 := fsc_logistic_lt_one t
  have hp0 : (0:ℝ) < fsc_logistic t := fsc_logistic_pos t
  have hc0 : 0 ≤ c := by
    rw [hc, neg_nonneg]; exact Real.log_nonpos (by linarith) (by linarith)
  have hEpos : ∀ j, 0 < agl_E d (agl_K j) := fun j => by
    unfold agl_E; exact_mod_cast hbox j
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have hMc0 : 0 ≤ M + c := by linarith
  have hIE0 : ∀ j, 0 ≤ I j / agl_E d (agl_K (j + 1)) := fun j =>
    div_nonneg (hInn j) (hEpos (j + 1)).le
  set δ : ℕ → ℝ := fun j => (M + c) * (I j / agl_E d (agl_K (j + 1))) with hδ
  
  apply agl_perVolume_converges
    (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) agl_K δ osc bj
  · intro j; exact mul_nonneg hMc0 (hIE0 j)
  · exact hIsum.mul_left (M + c)
  · 
    intro j
    rw [agl_g_eq d t (agl_K j), agl_g_eq d t (agl_K (j + 1))]
    have hKeq : agl_K (j + 1) = 2 * agl_K j + 1 := agl_K_succ j
    have hstep := bxt_perVolume_doubling_step (a := agl_u d t (agl_K j))
      (A := agl_u d t (agl_K (j + 1))) (e := agl_E d (agl_K j)) (E := agl_E d (agl_K (j + 1)))
      (K := (2 : ℝ) ^ d) (c := c) (i := I j)
      (hEpos j) (hEpos (j + 1)) hc0 (hInn j) (hudbl j) (hEdge j)
    have hdefle : (|agl_u d t (agl_K j)| / agl_E d (agl_K j) + c)
        * (I j / agl_E d (agl_K (j + 1))) ≤ δ j := by
      show _ ≤ (M + c) * (I j / agl_E d (agl_K (j + 1)))
      apply mul_le_mul_of_nonneg_right _ (hIE0 j)
      have habs : |agl_u d t (agl_K j)| / agl_E d (agl_K j)
          = |agl_u d t (agl_K j) / agl_E d (agl_K j)| := by
        rw [abs_div, abs_of_pos (hEpos j)]
      rw [habs]; have := hM j; linarith
    have hgoal : -(agl_u d t (agl_K j) / agl_E d (agl_K j)) - δ j
        ≤ -(agl_u d t (agl_K (j + 1)) / agl_E d (agl_K (j + 1))) := by linarith [hstep, hdefle]
    linarith
  · 
    refine ⟨M + Real.log (1 + Real.exp t), ?_⟩
    rintro x ⟨j, rfl⟩
    simp only
    rw [agl_g_eq d t (agl_K j)]
    have hlb : -M ≤ agl_u d t (agl_K j) / agl_E d (agl_K j) := (abs_le.mp (hM j)).1
    linarith
  · exact hbj
  · exact hosc
  · exact hsand


theorem agl_doublingStep_of_partition (t : ℝ) (K : ℕ) (P : boxVerts d (2 * K + 1) → Prop)
    [DecidablePred P] (v : Site d) (φ : boxVerts d K ≃ {x // P x})
    (hφ : ∀ y : boxVerts d K, ((φ y : boxVerts d (2 * K + 1)) : Site d) = (y : Site d) + v)
    (IR : ℝ) (hIR : 0 ≤ IR)
    (hRight : -Real.log (fkZ (agl_right (boxGraph d (2 * K + 1)) P) (fsc_logistic t) 2)
        ≤ ((2:ℝ) ^ d - 1) * agl_u d t K + IR * (-Real.log (1 - fsc_logistic t))) :
    agl_u d t (2 * K + 1)
      ≤ (2 : ℝ) ^ d * agl_u d t K
        + ((agl_interfaceCard (boxGraph d (2 * K + 1)) P : ℝ) + IR)
            * (-Real.log (1 - fsc_logistic t)) := by
  set p := fsc_logistic t with hp
  have hp0 : (0:ℝ) < p := fsc_logistic_pos t
  have hp1 : p < 1 := fsc_logistic_lt_one t
  
  have hpart := agl_neglog_partition_le (boxGraph d (2 * K + 1)) P hp0 hp1 (by norm_num : (0:ℝ) < 2)
  
  have hleft : fkZ (agl_left (boxGraph d (2 * K + 1)) P) p 2 = fkZ (boxGraph d K) p 2 :=
    agl_left_block_fkZ_eq (2 * K + 1) K P v φ hφ p 2
  have hleftu : -Real.log (fkZ (agl_left (boxGraph d (2 * K + 1)) P) p 2) = agl_u d t K := by
    rw [hleft]; rfl
  
  rw [hleftu] at hpart
  
  unfold agl_u at *
  nlinarith [hpart, hRight]


theorem agl_rightBlock_recursion_satisfiable (t : ℝ) (K : ℕ) (P : boxVerts d (2 * K + 1) → Prop)
    [DecidablePred P] :
    ∃ IR : ℝ, 0 ≤ IR ∧
      -Real.log (fkZ (agl_right (boxGraph d (2 * K + 1)) P) (fsc_logistic t) 2)
        ≤ ((2:ℝ) ^ d - 1) * agl_u d t K + IR * (-Real.log (1 - fsc_logistic t)) := by
  have hp0 : (0:ℝ) < fsc_logistic t := fsc_logistic_pos t
  have hp1 : fsc_logistic t < 1 := fsc_logistic_lt_one t
  have hclog : 0 < -Real.log (1 - fsc_logistic t) := by
    rw [neg_pos]; exact Real.log_neg (by linarith) (by linarith)
  
  set L := -Real.log (fkZ (agl_right (boxGraph d (2 * K + 1)) P) (fsc_logistic t) 2)
  set R0 := ((2:ℝ) ^ d - 1) * agl_u d t K
  refine ⟨max 0 ((L - R0) / (-Real.log (1 - fsc_logistic t))), le_max_left _ _, ?_⟩
  have hge : (L - R0) / (-Real.log (1 - fsc_logistic t))
      ≤ max 0 ((L - R0) / (-Real.log (1 - fsc_logistic t))) := le_max_right _ _
  have hmul : (L - R0) ≤ max 0 ((L - R0) / (-Real.log (1 - fsc_logistic t)))
      * (-Real.log (1 - fsc_logistic t)) := by
    rw [← div_le_iff₀ hclog]; exact hge
  linarith


end FK
end StatMech
