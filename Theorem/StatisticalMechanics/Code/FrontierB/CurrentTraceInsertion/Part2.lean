/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceInsertion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.BoxCurrentLaws.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentSelectionIndependence.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentMixingErgodicity.Part2
import Theorem.StatisticalMechanics.Code.FK.InfiniteFiniteEnergy.Part2
import Def.StatisticalMechanics.Code.FrontierB.CurrentTraceInsertion.Part2
open MeasureTheory
open scoped ENNReal BigOperators symmDiff


namespace StatMech.FrontierB

open Sharpness Lattice

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem currentTraceInsertionConstant_pos {beta : ℝ} (hbeta : 0 < beta) :
    0 < currentTraceInsertionConstant beta := by
  unfold currentTraceInsertionConstant
  positivity

theorem currentTraceInsertionConstant_le_one (beta : ℝ) :
    currentTraceInsertionConstant beta ≤ 1 := by
  unfold currentTraceInsertionConstant
  have hden : 0 < beta ^ 2 + 2 := by positivity
  apply (div_le_one hden).2
  linarith

set_option maxHeartbeats 800000 in

theorem currentPMF_map_forceCurrentEdgePositive_apply_bound
    (beta : ℝ) (hbeta : 0 < beta) (A : Finset V)
    (hA : 0 < currentSum G beta (fun _ => 1) A)
    (e : G.edgeFinset) (m : EdgeCurrent G) :
    ENNReal.ofReal (currentTraceInsertionConstant beta) *
        PMF.map (forceCurrentEdgePositive G e)
          (currentPMF G beta (fun _ => 1) hbeta.le
            (fun _ => zero_le_one) A hA) m ≤
      currentPMF G beta (fun _ => 1) hbeta.le
        (fun _ => zero_le_one) A hA m := by
  let p := currentPMF G beta (fun _ => 1) hbeta.le
    (fun _ => zero_le_one) A hA
  by_cases hm0 : m e = 0
  · rw [PMF.map_forceCurrentEdgePositive_apply_of_eq_zero G p e m hm0]
    simp
  by_cases hm2 : m e = 2
  · rw [PMF.map_forceCurrentEdgePositive_apply_of_eq_two G p e m hm2]
    let z := zeroCurrentEdge G e m
    have hz0 : z e = 0 := zeroCurrentEdge_apply_same G e m
    have hforce : forceCurrentEdgePositive G e z = m := by
      rw [forceCurrentEdgePositive_zeroCurrentEdge]
      funext f
      by_cases hfe : f = e
      · subst f
        simp [hm2]
      · simp [hfe]
    have hratio := currentPMF_forceCurrentEdgePositive_apply_of_zero
      G beta hbeta A hA e z hz0
    rw [hforce] at hratio
    change ENNReal.ofReal (currentTraceInsertionConstant beta) *
        (p m + p z) ≤ p m
    apply (ENNReal.toReal_le_toReal
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top p m, PMF.apply_ne_top p z⟩))
      (PMF.apply_ne_top p m)).mp
    have hratioReal := congrArg ENNReal.toReal hratio
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ beta ^ 2 / 2)]
      at hratioReal
    rw [ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (currentTraceInsertionConstant_pos hbeta).le,
      ENNReal.toReal_add (PMF.apply_ne_top p m) (PMF.apply_ne_top p z)]
    unfold currentTraceInsertionConstant
    have hden : 0 < beta ^ 2 + 2 := by positivity
    have htwo : (2 : ℝ) ≠ 0 := by norm_num
    field_simp
    nlinarith
  · rw [PMF.map_forceCurrentEdgePositive_apply_of_ne_two G p e m hm0 hm2]
    exact mul_le_of_le_one_left (by positivity)
      (ENNReal.ofReal_le_one.mpr (currentTraceInsertionConstant_le_one beta))

set_option maxHeartbeats 800000 in

theorem boundaryCurrentPMF_map_forceCurrentEdgePositive_apply_bound
    (beta : ℝ) (hbeta : 0 < beta) (interior : Finset V)
    (e : G.edgeFinset) (m : EdgeCurrent G) :
    ENNReal.ofReal (currentTraceInsertionConstant beta) *
        PMF.map (forceCurrentEdgePositive G e)
          (boundaryCurrentPMF G beta (fun _ => 1) hbeta.le
            (fun _ => zero_le_one) interior) m ≤
      boundaryCurrentPMF G beta (fun _ => 1) hbeta.le
        (fun _ => zero_le_one) interior m := by
  let p := boundaryCurrentPMF G beta (fun _ => 1) hbeta.le
    (fun _ => zero_le_one) interior
  by_cases hm0 : m e = 0
  · rw [PMF.map_forceCurrentEdgePositive_apply_of_eq_zero G p e m hm0]
    simp
  by_cases hm2 : m e = 2
  · rw [PMF.map_forceCurrentEdgePositive_apply_of_eq_two G p e m hm2]
    let z := zeroCurrentEdge G e m
    have hz0 : z e = 0 := zeroCurrentEdge_apply_same G e m
    have hforce : forceCurrentEdgePositive G e z = m := by
      rw [forceCurrentEdgePositive_zeroCurrentEdge]
      funext f
      by_cases hfe : f = e
      · subst f
        simp [hm2]
      · simp [hfe]
    have hratio := boundaryCurrentPMF_forceCurrentEdgePositive_apply_of_zero
      G beta hbeta interior e z hz0
    rw [hforce] at hratio
    change ENNReal.ofReal (currentTraceInsertionConstant beta) *
        (p m + p z) ≤ p m
    apply (ENNReal.toReal_le_toReal
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top p m, PMF.apply_ne_top p z⟩))
      (PMF.apply_ne_top p m)).mp
    have hratioReal := congrArg ENNReal.toReal hratio
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ beta ^ 2 / 2)]
      at hratioReal
    rw [ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (currentTraceInsertionConstant_pos hbeta).le,
      ENNReal.toReal_add (PMF.apply_ne_top p m) (PMF.apply_ne_top p z)]
    unfold currentTraceInsertionConstant
    have hden : 0 < beta ^ 2 + 2 := by positivity
    have htwo : (2 : ℝ) ≠ 0 := by norm_num
    field_simp
    nlinarith
  · rw [PMF.map_forceCurrentEdgePositive_apply_of_ne_two G p e m hm0 hm2]
    exact mul_le_of_le_one_left (by positivity)
      (ENNReal.ofReal_le_one.mpr (currentTraceInsertionConstant_le_one beta))


theorem PMF.toMeasure_map_le_of_apply_le
    {alpha : Type*} [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    (p : PMF alpha) (f : alpha → alpha) (c : ℝ≥0∞)
    (hpoint : ∀ a, c * PMF.map f p a ≤ p a)
    (S : Set alpha) :
    c * (PMF.map f p).toMeasure S ≤ p.toMeasure S := by
  rw [PMF.toMeasure_apply_eq_tsum, PMF.toMeasure_apply_eq_tsum,
    ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro a
  by_cases ha : a ∈ S
  · simpa [Set.indicator_of_mem ha] using hpoint a
  · simp [ha]

theorem currentPMF_forceCurrentEdgePositive_event_bound
    (beta : ℝ) (hbeta : 0 < beta) (A : Finset V)
    (hA : 0 < currentSum G beta (fun _ => 1) A)
    (e : G.edgeFinset) (S : Set (EdgeCurrent G)) :
    ENNReal.ofReal (currentTraceInsertionConstant beta) *
        (PMF.map (forceCurrentEdgePositive G e)
          (currentPMF G beta (fun _ => 1) hbeta.le
            (fun _ => zero_le_one) A hA)).toMeasure S ≤
      (currentPMF G beta (fun _ => 1) hbeta.le
        (fun _ => zero_le_one) A hA).toMeasure S := by
  exact PMF.toMeasure_map_le_of_apply_le
    (currentPMF G beta (fun _ => 1) hbeta.le
      (fun _ => zero_le_one) A hA)
    (forceCurrentEdgePositive G e)
    (ENNReal.ofReal (currentTraceInsertionConstant beta))
    (currentPMF_map_forceCurrentEdgePositive_apply_bound
      G beta hbeta A hA e) S

theorem boundaryCurrentPMF_forceCurrentEdgePositive_event_bound
    (beta : ℝ) (hbeta : 0 < beta) (interior : Finset V)
    (e : G.edgeFinset) (S : Set (EdgeCurrent G)) :
    ENNReal.ofReal (currentTraceInsertionConstant beta) *
        (PMF.map (forceCurrentEdgePositive G e)
          (boundaryCurrentPMF G beta (fun _ => 1) hbeta.le
            (fun _ => zero_le_one) interior)).toMeasure S ≤
      (boundaryCurrentPMF G beta (fun _ => 1) hbeta.le
        (fun _ => zero_le_one) interior).toMeasure S := by
  exact PMF.toMeasure_map_le_of_apply_le
    (boundaryCurrentPMF G beta (fun _ => 1) hbeta.le
      (fun _ => zero_le_one) interior)
    (forceCurrentEdgePositive G e)
    (ENNReal.ofReal (currentTraceInsertionConstant beta))
    (boundaryCurrentPMF_map_forceCurrentEdgePositive_apply_bound
      G beta hbeta interior e) S


end StatMech.FrontierB
